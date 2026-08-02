"""ONE recogniser for "what is a Lean declaration", with a self-test battery.

WHY THIS FILE EXISTS.  Paper 14 v1.0 printed a declaration count produced by a
regex blind to `@[simp] theorem`, and the same blindness certified "every
declaration is in the oracle" while two declarations were in fact absent.  The
first fix patched the regex in TWO places that had already drifted apart.  Two
graders with two grammars is the defect one level up.

WHY IT HAS ONE TRAVERSAL AND NOT TWO.  The first version of this file had one
grammar but still TWO walks over the text: `declarations` scanned comments
character by character, while `declaration_lines` --- the function the paper's
filler actually calls --- re-counted `/-` and `-/` per line and then matched the
RAW line.  Its docstring claimed "same grammar and same comment tracking"; that
was false, and an external reading produced the witness:

    /- doc -/theorem after_comment : True := trivial

which `declarations` sees and `declaration_lines` did not.  Two routes is two
graders again, one level further down, and the self-test covered only one of
them.  So there is now exactly one traversal, `iter_declarations`, yielding
`(name, line)`; the other two functions are projections of it, and the battery
checks names AND line numbers.

STATED SCOPE, because a certificate that overstates its reach is worse than
none.  This is a line-oriented recogniser over comment-stripped text, not a Lean
parser.  It handles attribute blocks on the declaration's line and on preceding
lines, the modifiers below in any order, nested block comments, and line
comments.  It does NOT handle declarations indented inside a section, `where`
blocks that introduce names, mutual blocks, or macros expanding to
declarations.  The durable fix is to enumerate from the ELABORATED Lean
environment rather than from source text, and that is not done here.
"""
import io
import re
import sys

KEYWORDS = ("theorem", "lemma", "def", "abbrev", "instance", "structure",
            "inductive", "class", "opaque", "axiom")
MODIFIERS = ("noncomputable", "private", "protected", "partial", "unsafe",
             "scoped", "local")

_ATTR = re.compile(r"^\s*@\[[^\]]*\]\s*")
_ATTR_ONLY = re.compile(r"^\s*@\[[^\]]*\]\s*$")
_DECL = re.compile(
    r"^(?:(?:%s)\s+)*(?:%s)\s+([A-Za-z_][A-Za-z0-9_'!?]*)"
    % ("|".join(MODIFIERS), "|".join(KEYWORDS)))


def declaration_name(line):
    """The name a single COMMENT-FREE source line declares, or None."""
    if _ATTR_ONLY.match(line):
        return None
    stripped = _ATTR.sub("", line) if _ATTR.match(line) else line
    if stripped.startswith(" ") or stripped.startswith("\t"):
        return None
    m = _DECL.match(stripped)
    return m.group(1) if m else None


def _strip_comments(line, depth):
    """Return (code outside comments, new depth).  Lean block comments NEST."""
    pieces = []
    i, n = 0, len(line)
    code_start = 0 if depth == 0 else None
    while i < n:
        two = line[i:i + 2]
        if two == "/-":
            if depth == 0 and code_start is not None:
                pieces.append(line[code_start:i])
                code_start = None
            depth += 1
            i += 2
            continue
        if two == "-/":
            if depth > 0:
                depth -= 1
                i += 2
                if depth == 0:
                    code_start = i
                continue
        if depth == 0 and two == "--":
            if code_start is not None:
                pieces.append(line[code_start:i])
                code_start = None
            break
        i += 1
    if depth == 0 and code_start is not None:
        pieces.append(line[code_start:])
    return "".join(pieces), depth


def iter_declarations(path):
    """THE single traversal.  Yields `(name, 1-based line)` in source order.

    Everything else in this module is a projection of this generator, so the
    two consumers cannot see different files.
    """
    depth = 0
    with io.open(path, encoding="utf-8", newline="") as f:
        for n, raw in enumerate(f, 1):
            code, depth = _strip_comments(raw, depth)
            if not code.strip():
                continue
            name = declaration_name(code)
            if name is not None:
                yield name, n


def declarations(path):
    """Every declaration name, in source order, without repeats."""
    out = []
    for name, _line in iter_declarations(path):
        if name not in out:
            out.append(name)
    return out


def declaration_lines(path):
    """name -> 1-based source line, first occurrence winning."""
    out = {}
    for name, line in iter_declarations(path):
        if name not in out:
            out[name] = line
    return out


CASES = [
    ("theorem foo : True := trivial", "foo"),
    ("lemma foo_bar : True := trivial", "foo_bar"),
    ("def baz : Nat := 0", "baz"),
    ("abbrev qux := Nat", "qux"),
    ("instance inst_a : Inhabited Nat := ⟨0⟩", "inst_a"),
    ("structure S where", "S"),
    ("inductive I where", "I"),
    ("class C where", "C"),
    ("noncomputable def nc : Nat := 0", "nc"),
    ("private theorem p : True := trivial", "p"),
    ("protected theorem q : True := trivial", "q"),
    ("noncomputable private def r : Nat := 0", "r"),
    ("@[simp] theorem s : True := trivial", "s"),
    ("@[simp, norm_cast] theorem t : True := trivial", "t"),
    ("@[simp] noncomputable def u : Nat := 0", "u"),
    ("@[simp]", None),
    ("  theorem indented : True := trivial", None),
    ("example : True := trivial", None),
    ("theorem prime' : True := trivial", "prime'"),
    ("", None),
]

# Whole-file cases, checked for NAMES AND LINE NUMBERS, because the defect this
# battery exists to prevent lived in the line-number route only.
FILE_CASES = [
    ("prose that begins with a keyword",
     "/-!\nThe Osterwalder--Schrader\naxiom asks for more.\n-/\ntheorem real_one : True := trivial\n",
     [("real_one", 5)]),
    ("nested block comments",
     "/- outer /- inner def hidden -/ still outer def also_hidden -/\ndef visible : Nat := 0\n",
     [("visible", 2)]),
    ("docstring immediately before a declaration",
     "/-- a docstring naming theorem ghost -/\ntheorem kept : True := trivial\n",
     [("kept", 2)]),
    ("attribute on its own line",
     "@[simp]\ntheorem attributed : True := trivial\n",
     [("attributed", 2)]),
    ("trailing line comment after code",
     "def d : Nat := 0 -- def not_this\n",
     [("d", 1)]),
    # the witness an external reading produced: code AFTER a closing comment
    # delimiter, on the same line.  The old line-number route lost it.
    ("declaration on the same line as a closing comment",
     "/- doc -/theorem after_comment : True := trivial\n",
     [("after_comment", 1)]),
    ("comment closing then opening again on one line",
     "/- a -/def one : Nat := 0\n/- b\nstill comment def hidden\n-/def two : Nat := 0\n",
     [("one", 1), ("two", 4)]),
    ("line comment before a real declaration",
     "-- theorem commented : True\ntheorem present : True := trivial\n",
     [("present", 2)]),
]


def selftest():
    import os
    import tempfile
    ran = 0
    bad = []
    for line, expected in CASES:
        ran += 1
        got = declaration_name(line)
        if got != expected:
            bad.append("line case %r -> %r, expected %r"
                       % (line[:40], got, expected))
    for name, body, expected in FILE_CASES:
        fd, path = tempfile.mkstemp(suffix=".lean")
        os.close(fd)
        io.open(path, "w", encoding="utf-8", newline="").write(body)
        try:
            pairs = list(iter_declarations(path))
            names = declarations(path)
            linemap = declaration_lines(path)
        finally:
            os.remove(path)
        ran += 1
        if pairs != expected:
            bad.append("%s: iter -> %r, expected %r" % (name, pairs, expected))
        ran += 1
        if names != [n for n, _ in expected]:
            bad.append("%s: names -> %r" % (name, names))
        ran += 1
        if linemap != dict(expected):
            bad.append("%s: lines -> %r, expected %r"
                       % (name, linemap, dict(expected)))
    total = len(CASES) + 3 * len(FILE_CASES)
    if ran != total:
        print("case counter disagrees: %d of %d" % (ran, total))
        return 2
    print("cases run: %d (%d line, %d whole-file x 3 projections)"
          % (ran, len(CASES), len(FILE_CASES)))
    if bad:
        for b in bad:
            print("FAILED:", b)
        return 1
    print("all pass -- ONE traversal, and names and line numbers are checked"
          " together so the two projections cannot drift")
    return 0


if __name__ == "__main__":
    sys.exit(selftest())
