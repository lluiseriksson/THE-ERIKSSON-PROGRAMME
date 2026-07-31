"""Is the CODE of a Lean module identical between two commits, comments aside?

Written because paper 13 v1.4 had to publish counters measured at one commit
while the checkpoint it ships is another, the two differing only in prose.  That
is a claim a reader must be able to re-run, so this takes BOTH revisions from
git rather than comparing a commit against whatever happens to be in the working
tree, and it takes the repository as an argument rather than carrying one
machine's absolute path.

    python scripts/check_code_identical.py <repo> <rev-a> <rev-b> [path]

Default path: YangMills/OS/SpatialOS.lean.  Exit code 0 if the two revisions
agree once every comment is stripped, 1 if they differ, 2 if git fails.
"""
import subprocess
import sys

DEFAULT_PATH = "YangMills/OS/SpatialOS.lean"


def strip_comments(src: str) -> str:
    """Drop `--` line comments and nested `/- -/` blocks, then normalise space.

    Whitespace is collapsed so that RE-WRAPPING a comment cannot be mistaken for
    a code change.
    """
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
    return " ".join("".join(out).split())


def blob(repo: str, rev: str, path: str) -> str:
    r = subprocess.run(["git", "show", "%s:%s" % (rev, path)], cwd=repo,
                       capture_output=True)
    if r.returncode != 0:
        print("git show %s:%s failed: %s"
              % (rev, path, r.stderr.decode(errors="replace").strip()))
        sys.exit(2)
    return r.stdout.decode("utf-8")


def main() -> int:
    if len(sys.argv) < 4:
        print(__doc__)
        return 2
    repo, rev_a, rev_b = sys.argv[1], sys.argv[2], sys.argv[3]
    path = sys.argv[4] if len(sys.argv) > 4 else DEFAULT_PATH

    a = strip_comments(blob(repo, rev_a, path))
    b = strip_comments(blob(repo, rev_b, path))

    print("path :", path)
    print("rev A:", rev_a, "->", len(a), "code chars")
    print("rev B:", rev_b, "->", len(b), "code chars")
    if a == b:
        print("IDENTICAL once comments are stripped")
        return 0
    for k in range(min(len(a), len(b))):
        if a[k] != b[k]:
            print("first difference at char", k)
            print("  A:", a[max(0, k - 60):k + 60])
            print("  B:", b[max(0, k - 60):k + 60])
            break
    else:
        print("one is a prefix of the other; lengths differ")
    print("DIFFERENT")
    return 1


if __name__ == "__main__":
    sys.exit(main())
