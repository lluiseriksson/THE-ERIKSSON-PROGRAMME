"""Is the CODE identical to the measured checkpoint, comments aside?

The v1.4 edits to the module are prose only.  Saying so is an assertion; this
strips every comment from both blobs and diffs what is left, which a reader can
re-run.  If the output is empty, the declarations elaborated at the measured
commit are byte-identical to the ones being published.
"""
import subprocess
import sys

REPO = r"C:\Users\lluis\AppData\Local\Temp\eriksson-push2"
PATH = "YangMills/OS/SpatialOS.lean"
MEASURED = sys.argv[1]


def strip_comments(src: str) -> str:
    out, i, depth = [], 0, 0
    n = len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif src.startswith("-/", i):
            depth = max(0, depth - 1)
            i += 2
        elif depth == 0 and src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        else:
            if depth == 0:
                out.append(src[i])
            i += 1
    # collapse whitespace so that re-wrapping of comments cannot show up
    return " ".join("".join(out).split())


def blob(rev):
    r = subprocess.run(["git", "show", f"{rev}:{PATH}"], cwd=REPO,
                       capture_output=True)
    return r.stdout.decode("utf-8")


old = strip_comments(blob(MEASURED))
new = strip_comments(open(REPO + "\\" + PATH.replace("/", "\\"),
                          encoding="utf-8").read())
print("measured commit :", MEASURED)
print("code chars (measured / working):", len(old), "/", len(new))
if old == new:
    print("IDENTICAL once comments are stripped")
    sys.exit(0)
for k in range(min(len(old), len(new))):
    if old[k] != new[k]:
        print("first difference at char", k)
        print("  measured:", old[max(0, k - 60):k + 60])
        print("  working :", new[max(0, k - 60):k + 60])
        break
sys.exit(1)
