r"""Refuse any text file GIVEN ON THE COMMAND LINE that carries a control byte.

WHY THIS EXISTS, and the answer is embarrassing.  A manuscript section was
inserted through a `python -c "..."` command line: the shell consumed one level
of backslashes and Python consumed another, so `\\beta` became U+0008 BACKSPACE
and `\\rVert` became U+000D CARRIAGE RETURN.  Thirteen backspaces and four
carriage returns went into the committed `.tex`.  `\begin{theorem}` stopped
existing as a command while `\end{theorem}` survived, so the document could not
compile --- and NOTHING in the pipeline noticed, because every existing guard
reads the file as text and control characters are text.

This was the FIFTH time escape handling corrupted a file in one working
session, and the rule written down after the first three --- scripts go in
files, never in a command line or a heredoc --- had been broken again.  A rule
that is only written down is not a guard.  This is the guard.

Permitted: tab (0x09), newline (0x0A), and a carriage return that is IMMEDIATELY
FOLLOWED BY a newline.  Everything else below 0x20, plus DEL (0x7F), is refused.

The carriage-return rule is the one that needed thought, and the first version
of this file got it wrong in the direction this repository keeps punishing: it
refused every CR outright, declaring that "these files are stored with LF".
They are stored with LF in the repository and checked out with CRLF on the
owner's desktop, so the guard failed on two perfectly clean files with 1699 and
3292 line endings apiece.  A guard that cries on correct input gets switched
off.  What actually distinguishes the defect is that a mangled `\r` escape
produces a LONE carriage return; a line ending is always CR immediately
followed by LF.

    python scripts/check_no_control_bytes.py <file> [<file> ...]

Exit 1 if any file carries a control byte, in normal and `-O` modes alike.  No
acceptance decision depends on `assert`.
"""
import io
import os
import sys

ALLOWED = {0x09, 0x0A}
NAMES = {0x00: "NUL", 0x07: "BEL", 0x08: "BACKSPACE", 0x0B: "VT", 0x0C: "FF",
         0x0D: "CARRIAGE RETURN", 0x1B: "ESC", 0x7F: "DEL"}


def offenders_bytes(raw):
    """THE single traversal.  `(byte, line, column)` for every control byte
    that is not part of a line ending.

    Everything else in this module and in `fill_p14.py` is a caller of this
    function.  The first version had the filler carry its OWN copy of the rule,
    which dropped every carriage return instead of only the ones followed by a
    newline --- so the standalone guard rejected a lone CR and the publisher
    accepted it.  Two semantics for one rule is the defect this repository has
    now met at three different levels; one function is the fix.
    """
    out = []
    line, col = 1, 1
    n = len(raw)
    for i, b in enumerate(raw):
        if b == 0x0A:
            line += 1
            col = 1
            continue
        if b == 0x0D:
            # CR immediately followed by LF is a line ending, not a mangled
            # escape.  A LONE CR is the defect this guard exists for.
            if i + 1 < n and raw[i + 1] == 0x0A:
                continue
            out.append((b, line, col))
            col += 1
            continue
        if (b < 0x20 and b not in ALLOWED) or b == 0x7F:
            out.append((b, line, col))
        col += 1
    return out


def offenders(path):
    """The same rule, applied to a file.  A projection, not a second grammar."""
    return offenders_bytes(io.open(path, "rb").read())


# Fixtures committed with the guard, so its behaviour is reproducible from the
# anchor instead of resting on a run someone did by hand once.
FIXTURES = [
    ("LF only", b"a\nb\n", []),
    ("CRLF only", b"a\r\nb\r\n", []),
    ("tab", b"a\tb\n", []),
    ("lone CR", b"a\rb", [0x0D]),
    ("CR at end of file", b"a\r", [0x0D]),
    ("BACKSPACE", b"a\x08b", [0x08]),
    ("NUL", b"a\x00b", [0x00]),
    ("DEL", b"a\x7fb", [0x7F]),
    ("ESC", b"a\x1bb", [0x1B]),
    ("mixed CRLF and lone CR", b"a\r\nb\rc\r\n", [0x0D]),
]


def selftest():
    ran = 0
    bad = []
    for name, raw, expected in FIXTURES:
        ran += 1
        got = [b for b, _l, _c in offenders_bytes(raw)]
        if got != expected:
            bad.append("%s -> %r, expected %r" % (name, got, expected))
    if ran != len(FIXTURES):
        print("fixture counter disagrees: %d of %d" % (ran, len(FIXTURES)))
        return 2
    print("fixtures run: %d" % ran)
    if bad:
        for b in bad:
            print("FAILED:", b)
        return 1
    print("all fixtures pass: CRLF is a line ending, a LONE CR is not")
    return 0


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        return selftest()
    if len(sys.argv) < 2:
        print("usage: check_no_control_bytes.py <file> [<file> ...]")
        print("       check_no_control_bytes.py --self-test")
        return 2
    ran = 0
    bad = []
    for path in sys.argv[1:]:
        ran += 1
        if not os.path.exists(path):
            bad.append("%s: missing" % path)
            continue
        hits = offenders(path)
        if hits:
            counts = {}
            for b, _l, _c in hits:
                counts[b] = counts.get(b, 0) + 1
            for b, n in sorted(counts.items()):
                first = next(h for h in hits if h[0] == b)
                bad.append("%s: 0x%02X %s x%d, first at line %d col %d"
                           % (path, b, NAMES.get(b, "control"), n,
                              first[1], first[2]))
        else:
            print("  clean: %s" % path)
    if ran != len(sys.argv) - 1:
        print("file counter disagrees: %d of %d" % (ran, len(sys.argv) - 1))
        return 2
    print("files checked: %d" % ran)
    if bad:
        for b in bad:
            print("FAILED:", b)
        print("a control byte in a source file is a mangled escape, not data")
        return 1
    print("no forbidden control bytes: tab, newline and CRLF only")
    return 0


if __name__ == "__main__":
    sys.exit(main())
