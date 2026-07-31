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
    """Drop `--` line comments and nested `/- -/` blocks, keeping ALL other space.

    Indentation is syntax in Lean: `by`, `do` and structure instances are column
    sensitive, so a comparator that collapses whitespace could call two files
    identical when they parse differently.  An earlier version of this script did
    exactly that.  Here every character outside a comment is preserved verbatim,
    including leading whitespace, and only lines that become entirely blank are
    dropped --- blank lines carry no column information, so removing them makes
    the check insensitive to how long a comment was without weakening it.

    String literals are respected, so `--` and `/-` inside a string do not open
    a comment.

    A comment is replaced by SPACES OF ITS OWN WIDTH, one per character, not by
    nothing and not by a single space.  Deleting it outright would map
    `foo/- c -/bar` and `foobar` to the same text although the first is two
    identifiers and the second is one.  Collapsing it to one space would erase
    the column at which the code AFTER an inline comment sits, and in Lean a
    column decides whether a token belongs to a nested block.  Newlines inside a
    comment are kept, so line structure is never joined.

    The line clean-up below --- dropping trailing space and blank lines --- is
    applied ONLY to lines that contain no string-literal character.  A Lean
    string may hold literal newlines and trailing spaces, and those are program
    DATA; an earlier version rstripped them and so identified
    `"a  \\n b"` with `"a\\n b"`, which is a false positive.

    SCOPE, stated because a certificate that overstates its reach is worse than
    none: this scanner models ORDINARY string literals with backslash escapes.
    It does not model raw strings or interpolation, and it is not a Lean lexer.
    Within that fragment --- which is the fragment `SpatialOS.lean` uses --- it
    errs only towards reporting a difference that is not one.
    """
    chars, prot = [], []          # parallel: prot[k] iff chars[k] is string data

    def put(ch, inside=False):
        chars.append(ch)
        prot.append(inside)

    i, depth, n = 0, 0, len(src)
    while i < n:
        if depth == 0 and src[i] == '"':
            put(src[i], True)
            i += 1
            while i < n:
                if src[i] == "\\" and i + 1 < n:
                    put(src[i], True)
                    put(src[i + 1], True)
                    i += 2
                    continue
                c = src[i]
                put(c, True)
                i += 1
                if c == '"':
                    break
        elif src.startswith("/-", i):
            depth += 1
            put(" ")
            put(" ")
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            put(" ")
            put(" ")
            i += 2
        elif depth == 0 and src.startswith("--", i):
            while i < n and src[i] != "\n":
                put(" ")
                i += 1
        else:
            if depth == 0:
                put(src[i])
            else:
                put("\n" if src[i] == "\n" else " ")
            i += 1

    # Split into lines, remembering whether any character of the line -- or the
    # newline that ended it -- was string data.
    lines, cur, guarded = [], [], False
    for ch, p in zip(chars, prot):
        if ch == "\n":
            lines.append(("".join(cur), guarded or p))
            cur, guarded = [], False
        else:
            cur.append(ch)
            guarded = guarded or p
    lines.append(("".join(cur), guarded))

    kept = []
    for text, guarded in lines:
        if guarded:
            kept.append(text)          # verbatim: this is program data
        else:
            trimmed = text.rstrip()
            if trimmed:
                kept.append(trimmed)
    return "\n".join(kept)


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
