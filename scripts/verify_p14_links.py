"""Verify paper 14's permalinks THREE WAYS, as this lane's practice requires.

  1. against the BLOB at the anchor: the cited line of the cited file must
     actually begin the cited declaration, read from `git show <anchor>:<path>`
     rather than from the working tree, because the working tree can have moved;
  2. inside the COMPILED PDF: the same URLs must be the ones a reader clicks,
     not the ones the source intended;
  3. LIVE over HTTP: each URL must resolve.

A link checked only in the source is not checked.  A link checked only in the
PDF cannot say whether the line is right.  A link checked only over HTTP says
the file exists, not that the line holds the theorem.  All three, or none.

No acceptance decision depends on `assert`.  Exit 1 on any failure, in normal
and `-O` modes alike.

    python scripts/verify_p14_links.py <anchor-sha> [--no-http]
"""
import io
import os
import re
import subprocess
import sys
import urllib.request

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TEX = os.path.join(REPO, "papers", "spatial-reconstruction",
                   "spatial_reconstruction.tex")
PDF = os.path.join(REPO, "papers", "spatial-reconstruction",
                   "spatial_reconstruction.pdf")
BASE = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/"

OSLINE = re.compile(r"\\osline\{([A-Za-z]+)\}\{(\d+)\}\{([^}]*)\}")
REPOFILE = re.compile(r"\\repofile\{([^}]*)\}\{([^}]*)\}")


def unescape(tex_name):
    return tex_name.replace("\\_", "_").replace("\\&", "&")


def git_show(anchor, path):
    r = subprocess.run(["git", "show", "%s:%s" % (anchor, path)], cwd=REPO,
                       capture_output=True)
    if r.returncode != 0:
        return None
    return r.stdout.decode("utf-8", "replace").splitlines()


def main():
    if len(sys.argv) < 2:
        print("usage: verify_p14_links.py <anchor-sha> [--no-http]")
        return 2
    anchor = sys.argv[1].strip()
    do_http = "--no-http" not in sys.argv[2:]

    tex = io.open(TEX, encoding="utf-8", newline="").read()
    checks = []
    urls = []

    # ---- 1. the blob at the anchor
    for mod, line_s, name in OSLINE.findall(tex):
        path = "YangMills/OS/%s.lean" % mod
        decl = unescape(name)
        line = int(line_s)
        body = git_show(anchor, path)
        ok_file = body is not None
        checks.append(("blob exists at anchor: %s" % path, ok_file))
        if not ok_file:
            continue
        ok_line = 1 <= line <= len(body)
        checks.append(("line in range: %s:%d" % (path, line), ok_line))
        if ok_line:
            text = body[line - 1]
            checks.append(("line %d of %s declares %s" % (line, path, decl),
                           re.search(r"\b%s\b" % re.escape(decl), text)
                           is not None))
        urls.append("%s%s/%s#L%d" % (BASE, anchor, path, line))

    for path_tex, _shown in REPOFILE.findall(tex):
        path = unescape(path_tex)
        checks.append(("blob exists at anchor: %s" % path,
                       git_show(anchor, path) is not None))
        urls.append("%s%s/%s" % (BASE, anchor, path))

    # ---- 2. inside the compiled PDF
    pdf_ok = os.path.exists(PDF)
    checks.append(("compiled PDF present", pdf_ok))
    if pdf_ok:
        raw = io.open(PDF, "rb").read().decode("latin-1")
        for u in urls:
            # hyperref may split long URIs across lines in the object stream
            flat = re.sub(r"[\r\n\\]", "", raw)
            checks.append(("URL present in PDF: %s" % u[-60:],
                           re.sub(r"[\r\n\\]", "", u) in flat))
        checks.append(("no stale anchor in PDF",
                       len(set(re.findall(r"/blob/([0-9a-f]{40})/", raw))
                           - {anchor}) == 0))

    # ---- 3. live over HTTP
    if do_http:
        for u in sorted(set(urls)):
            try:
                req = urllib.request.Request(u, method="HEAD",
                                             headers={"User-Agent": "p14-verify"})
                code = urllib.request.urlopen(req, timeout=30).status
            except Exception as exc:                      # noqa: BLE001
                code = "error: %s" % exc
            checks.append(("HTTP 200: %s" % u[-60:], code == 200))

    ran = 0
    failed = []
    for name, ok in checks:
        ran += 1
        if not ok:
            failed.append(name)
    if ran != len(checks):
        print("check counter disagrees: %d of %d" % (ran, len(checks)))
        return 2
    print("checks run: %d  (blob + PDF%s)" % (ran, " + HTTP" if do_http else ""))
    if failed:
        for name in failed:
            print("FAILED:", name)
        return 1
    print("all permalinks verified three ways" if do_http
          else "all permalinks verified against blob and PDF (HTTP skipped)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
