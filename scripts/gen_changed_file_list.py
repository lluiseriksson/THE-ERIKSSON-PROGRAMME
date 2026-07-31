"""Write a paper's changed-file list FROM `git diff --name-only`, never by hand.

Twice that sentence was written from memory with the command's output on screen,
and twice it was wrong: once omitting a generated file, once naming a file that
had never been touched.  A list a human types is a claim ABOUT the command; a
list this script derives IS the command.

    python scripts/gen_changed_file_list.py <repo> <tex> <measured-rev> <anchor-rev> [lean-path]

Default lean-path: YangMills/OS/SpatialOS.lean.  The script asserts the Lean
file is present in the diff, since the whole paragraph exists to say which
elaborated file changed.  Exit 0 on success, 2 if git fails or the paragraph
markers are absent.
"""
import io
import subprocess
import sys

DEFAULT_LEAN = "YangMills/OS/SpatialOS.lean"

# The paragraph this script owns: recognised by its opening words and ended by
# the sentence that follows it.  Both markers live in the .tex.
START = "Between that commit and this checkpoint"
END = "That is a checkable claim"


def tt(path: str) -> str:
    return r"\texttt{" + path.replace("_", r"\_") + "}"


def main() -> int:
    if len(sys.argv) < 5:
        print(__doc__)
        return 2
    repo, tex, measured, anchor = sys.argv[1:5]
    lean = sys.argv[5] if len(sys.argv) > 5 else DEFAULT_LEAN

    r = subprocess.run(["git", "diff", "--name-only", measured, anchor],
                       cwd=repo, capture_output=True)
    if r.returncode != 0:
        print("git diff failed:", r.stderr.decode(errors="replace").strip())
        return 2
    files = [f for f in r.stdout.decode().split() if f]
    if not files:
        print("empty diff between", measured, "and", anchor)
        return 2
    if lean not in files:
        print("the Lean file", lean, "is not in the diff")
        return 2

    others = [f for f in files if f != lean]
    if len(others) > 1:
        listing = ", ".join(tt(f) for f in others[:-1]) + " and " + tt(others[-1])
    elif others:
        listing = tt(others[0])
    else:
        listing = "nothing else"

    para = (r"Between that commit and this checkpoint "
            r"\verb|git diff --name-only| returns exactly " + listing +
            r" together with " + tt(lean) +
            r""".  Only the last of those is elaborated, and it changed
\emph{only in comments}; the others are this manuscript in its previous version,
the ledger, the comparison script and a generated dashboard, none of which Lean
ever sees.  This list is produced from the command's output rather than typed,
because twice it was typed and twice it was wrong.""")

    t = io.open(tex, encoding="utf-8", newline="").read()
    nl = "\r\n" if "\r\n" in t else "\n"
    i = t.find(START)
    j = t.find(END, i + 1 if i >= 0 else 0)
    if i < 0 or j <= i:
        print("paragraph markers not found in", tex)
        return 2
    io.open(tex, "w", encoding="utf-8", newline="").write(
        t[:i] + para.replace("\n", nl) + nl + nl + t[j:])

    print("file list generated from the diff:")
    for f in files:
        print("   ", f)
    return 0


if __name__ == "__main__":
    sys.exit(main())
