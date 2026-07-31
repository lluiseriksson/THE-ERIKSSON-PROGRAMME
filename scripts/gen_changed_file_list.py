"""Generate the changed-file list in the paper FROM the diff, never by hand.

Twice now that sentence has been written from memory with the command's output
on screen, and twice it has been wrong: once omitting a generated file, once
naming a file that had never been touched.  A list a human types is a claim; a
list a script derives from `git diff --name-only` is the command's output.

    python p13_filelist.py <measured-rev> <anchor-rev>
"""
import io
import re
import subprocess
import sys

REPO = r"C:\Users\lluis\AppData\Local\Temp\eriksson-push2"
TEX = REPO + r"\papers\spatial-os\spatial_os.tex"

MEASURED, ANCHOR = sys.argv[1], sys.argv[2]

r = subprocess.run(["git", "diff", "--name-only", MEASURED, ANCHOR],
                   cwd=REPO, capture_output=True)
if r.returncode != 0:
    sys.exit("git diff failed: " + r.stderr.decode(errors="replace"))
files = [f for f in r.stdout.decode().split() if f]
assert files, "empty diff"

LEAN = "YangMills/OS/SpatialOS.lean"
assert LEAN in files, "the module is not in the diff"
others = [f for f in files if f != LEAN]


def tt(path):
    return r"\texttt{" + path.replace("_", r"\_") + "}"


listing = ", ".join(tt(f) for f in others[:-1])
listing += " and " + tt(others[-1]) if len(others) > 1 else tt(others[0])

new = (r"""Between that commit and this checkpoint \verb|git diff --name-only| returns
exactly """ + listing + r""" together with """ + tt(LEAN) + r""".  Only the last of
those is elaborated, and it changed \emph{only in comments}; the others are this
manuscript in its previous version, the ledger, the comparison script and a
generated dashboard, none of which Lean ever sees.  This list is produced from
the command's output rather than typed, because twice it was typed and twice it
was wrong.""")

t = io.open(TEX, encoding="utf-8", newline="").read()
nl = "\r\n" if "\r\n" in t else "\n"

pat = re.compile(
    r"Between that commit and this checkpoint the \\emph\{only\}.*?"
    r"returns exactly those files and \\texttt\{SpatialOS\.lean\}\.",
    re.S)
if not pat.search(t.replace(nl, "\n")):
    # first run: replace the hand-written paragraph
    old_start = "Between that commit and this checkpoint the \\emph{only}"
    i = t.find(old_start.replace("\n", nl))
    assert i >= 0, "anchor paragraph not found"
    j = t.find("That is a checkable claim".replace("\n", nl), i)
    assert j > i, "end of paragraph not found"
    t = t[:i] + new.replace("\n", nl) + nl + nl + t[j:]
else:
    t = pat.sub(lambda _: new, t.replace(nl, "\n")).replace("\n", nl)

io.open(TEX, "w", encoding="utf-8", newline="").write(t)
print("file list generated from the diff:")
for f in files:
    print("   ", f)
