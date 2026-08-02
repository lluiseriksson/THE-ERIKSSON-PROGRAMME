"""ONE grammar for "what is a Lean declaration", with a self-test battery.

WHY THIS FILE EXISTS.  Paper 14 v1.0 printed a declaration count produced by a
regex blind to `@[simp] theorem`, and the same blindness certified "every
declaration is in the oracle" while two declarations were in fact absent.  The
first fix patched the regex --- in TWO places, which had already drifted apart
(one accepted `protected`, the other did not).  Two graders with two grammars is
the defect one level up.

So: one grammar, in one file, imported by both consumers, with a battery of
syntactic cases that runs on `python scripts/lean_decls.py` and exits non-zero
if any case regresses.  A parser that once certified a false coverage should not
remain the unexamined root of trust; this does not make it sound, but it makes
its failures reproducible and its coverage visible.

STATED SCOPE, because a certificate that overstates its reach is worse than
none.  This is a line-oriented recogniser, not a Lean parser.  It handles
attribute blocks on the declaration's own line and on preceding lines, the
`noncomputable / private / protected / partial / unsafe / scoped / local`
modifiers in any order, and the declaration keywords listed below.  It does NOT
handle declarations indented inside a `section` with leading whitespace, `where`
blocks that introduce names, mutual blocks, or macros that expand to
declarations.  Within the fragment the S-block modules use, it errs towards
seeing MORE, never fewer.
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
    """The name a single source line declares, or None.

    An attribute block on the same line is stripped first; a line that is only
    an attribute block declares nothing by itself.
    """
    if _ATTR_ONLY.match(line):
        return None
    stripped = _ATTR.sub("", line) if _ATTR.match(line) else line
    if stripped.startswith(" ") or stripped.startswith("\t"):
        return None
    m = _DECL.match(stripped)
    return m.group(1) if m else None


def declarations(path):
    """Every declaration name in a module, in source order, without repeats.

    COMMENTS ARE TRACKED, and this was not optional.  The first version of this
    file read prose: the module header contains the sentence "The
    Osterwalder--Schrader axiom asks for more", whose second line begins with
    `axiom asks`, and the parser dutifully reported a declaration named `asks`.
    That is ghost class #26 --- a list that did not distinguish code from prose
    --- reproduced by the very file written to prevent it.  Lean block comments
    NEST, so the tracker counts depth rather than matching a single pair.
    """
    out = []
    depth = 0
    with io.open(path, encoding="utf-8", newline="") as f:
        for raw in f:
            line = raw
            if depth == 0:
                head = line.lstrip()
                if head.startswith("--"):
                    continue
            # walk the line counting comment openers and closers
            i, n, code_start = 0, len(line), 0 if depth == 0 else None
            pieces = []
            while i < n - 1:
                two = line[i:i + 2]
                if two == "/-":
                    if depth == 0 and code_start is not None:
                        pieces.append(line[code_start:i])
                        code_start = None
                    depth += 1
                    i += 2
                    continue
                if two == "-/":
                    depth = max(0, depth - 1)
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
            code = "".join(pieces)
            if not code.strip():
                continue
            name = declaration_name(code)
            if name is not None and name not in out:
                out.append(name)
    return out


def declaration_lines(path):
    """name -> 1-based source line, for every declaration in a module.

    Same grammar and same comment tracking as `declarations`; the two must not
    drift, which is why one is written in terms of the other.
    """
    out = {}
    names = declarations(path)
    remaining = set(names)
    depth = 0
    with io.open(path, encoding="utf-8", newline="") as f:
        for n, raw in enumerate(f, 1):
            if depth == 0 and raw.lstrip().startswith("--"):
                continue
            before = depth
            depth += raw.count("/-") - raw.count("-/")
            depth = max(0, depth)
            if before != 0:
                continue
            name = declaration_name(raw)
            if name in remaining:
                out[name] = n
                remaining.discard(name)
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
    ("@[simp]", None),                       # attribute on its own line
    ("  theorem indented : True := trivial", None),
    ("-- theorem commented : True", None),
    ("/-- a docstring mentioning theorem foo -/", None),
    ("example : True := trivial", None),
    ("theorem prime' : True := trivial", "prime'"),
    ("", None),
]


# Whole-file cases, which is where the prose defect lived: a single line cannot
# express "inside a block comment".
FILE_CASES = [
    ("prose that begins with a keyword",
     "/-!\nThe Osterwalder--Schrader\naxiom asks for more.\n-/\ntheorem real_one : True := trivial\n",
     ["real_one"]),
    ("nested block comments",
     "/- outer /- inner def hidden -/ still outer def also_hidden -/\ndef visible : Nat := 0\n",
     ["visible"]),
    ("docstring immediately before a declaration",
     "/-- a docstring naming theorem ghost -/\ntheorem kept : True := trivial\n",
     ["kept"]),
    ("attribute on its own line",
     "@[simp]\ntheorem attributed : True := trivial\n",
     ["attributed"]),
    ("trailing line comment after code",
     "def d : Nat := 0 -- def not_this\n",
     ["d"]),
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
            bad.append("%r -> %r, expected %r" % (line[:44], got, expected))
    for name, body, expected in FILE_CASES:
        ran += 1
        fd, path = tempfile.mkstemp(suffix=".lean")
        os.close(fd)
        io.open(path, "w", encoding="utf-8", newline="").write(body)
        try:
            got = declarations(path)
        finally:
            os.remove(path)
        if got != expected:
            bad.append("%s -> %r, expected %r" % (name, got, expected))
    total = len(CASES) + len(FILE_CASES)
    if ran != total:
        print("case counter disagrees: %d of %d" % (ran, total))
        return 2
    print("syntactic cases run: %d (%d line, %d whole-file)"
          % (ran, len(CASES), len(FILE_CASES)))
    if bad:
        for b in bad:
            print("FAILED:", b)
        return 1
    print("all cases pass -- attribute blocks, modifiers, primes; and prose,"
          " nested comments and `example` are NOT declarations")
    return 0


if __name__ == "__main__":
    sys.exit(selftest())
