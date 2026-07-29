"""Guard against the one defect the build cannot catch.

`lake build` checks the code.  Nothing checks what the module *says about
itself*: a docstring can name a theorem that was renamed, or advertise a
section number that no longer exists, and the build stays green.  This has now
been the flagged defect in three successive external readings of the S block,
so it gets a script instead of another promise.

Checks, for each module named on the command line:

  1. every backticked identifier in the module header (the leading `/-! ... -/`)
     that LOOKS like a Lean name resolves to a declaration somewhere in the
     lane (a header may legitimately cite a companion module it does not
     import, so the search is lane-wide rather than import-local);
  2. every section reference `§N` in the header corresponds to a `## §N`
     heading that actually exists in the file.

"Looks like a Lean name" means: at least three characters, and either
containing an underscore or mixing case.  Single letters and ordinary English
words are prose, not names, and flagging them would make the guard noise.

Exit code 1 on any failure.  Run:

    python scripts/check_module_prose.py YangMills/OS/SpatialSpectral.lean
"""
import re
import sys
import os

DECL = re.compile(r"^(?:noncomputable\s+)?(?:private\s+)?"
                  r"(?:theorem|def|lemma|abbrev|instance|structure|inductive|class)\s+"
                  r"([A-Za-z_][A-Za-z0-9_']*)")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
SUBSCRIPT = re.compile(r"^[A-Za-z]_[A-Za-z0-9]{1,2}$")   # `Z_2`, `Z_N`: notation
SECREF = re.compile(r"§(\d+)")


def looks_like_a_name(tok):
    """Distinguish a Lean declaration name from a prose word or a variable."""
    if not IDENT.match(tok) or len(tok) < 3 or SUBSCRIPT.match(tok):
        return False
    if "_" in tok:
        return True
    return tok.lower() != tok and tok.upper() != tok    # mixed case


def declarations(path):
    """Top-level declaration names, ignoring anything inside a block comment."""
    names, depth = set(), 0
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            i, keep = 0, []
            while i < len(line):
                if line.startswith("/-", i):
                    depth += 1
                    i += 2
                elif line.startswith("-/", i):
                    depth = max(0, depth - 1)
                    i += 2
                else:
                    if depth == 0:
                        keep.append(line[i])
                    i += 1
            m = DECL.match("".join(keep))
            if m:
                names.add(m.group(1))
    return names


def header(path):
    """The leading module docstring, as text."""
    src = open(path, encoding="utf-8").read()
    m = re.search(r"/-!(.*?)-/", src, re.S)
    return m.group(1) if m else ""


def sections(path):
    src = open(path, encoding="utf-8").read()
    return set(re.findall(r"##\s*§(\d+)", src))


_ALL = None


def all_names(repo):
    """Every declaration under YangMills/, plus every module name.

    Lane-wide is not enough: a header may legitimately cite a companion in
    another lane.  Built once and cached.
    """
    global _ALL
    if _ALL is None:
        _ALL = set()
        for root, _dirs, files in os.walk(os.path.join(repo, "YangMills")):
            for entry in files:
                if entry.endswith(".lean"):
                    _ALL |= declarations(os.path.join(root, entry))
                    _ALL.add(entry[:-5])
    return _ALL


_MATHLIB = None


def mathlib_names(repo):
    """Declarations in the pinned mathlib, so citing one is not a failure.

    Slow (a few seconds), so it is only built if some token missed the project
    set.  A header that cites `IsSelfAdjoint` is citing mathlib, not lying.
    """
    global _MATHLIB
    if _MATHLIB is None:
        _MATHLIB = set()
        root = os.path.join(repo, ".lake", "packages", "mathlib", "Mathlib")
        for base, _dirs, files in os.walk(root):
            for entry in files:
                if not entry.endswith(".lean"):
                    continue
                with open(os.path.join(base, entry), encoding="utf-8",
                          errors="replace") as fh:
                    for line in fh:
                        m = DECL.match(line)
                        if m:
                            _MATHLIB.add(m.group(1))
    return _MATHLIB


def check(repo, rel):
    fails = []
    path = os.path.join(repo, rel.replace("/", os.sep))
    known = all_names(repo)
    head = header(path)

    # (1) backticked identifiers.  A name introduced to say it does NOT exist
    # ("there is no `Complexification` anywhere under ...") is not a defect --
    # its absence is the claim -- so an explicit negation just before the
    # backtick exempts it.
    for m in re.finditer(r"`([^`\n]+)`", head):
        tok = m.group(1).strip()
        if not looks_like_a_name(tok) or tok in known:
            continue
        before = re.sub(r"\s+", " ", head[max(0, m.start() - 40):m.start()])
        if re.search(r"(there (is|was|are|were) no|no such|does not exist"
                     r"|nothing called) $", before, re.I):
            continue
        if tok in mathlib_names(repo):
            continue
        fails.append("header names `%s`, which is no declaration under "
                     "YangMills/ nor in mathlib" % tok)

    # (2) section cross-references.  Only meaningful in a file that numbers its
    # own sections; elsewhere a `§N` is a citation to somebody else's book.
    have = sections(path)
    if have:
        for n in sorted(set(SECREF.findall(head))):
            if n not in have:
                fails.append("header refers to section %s, which is not a "
                             "heading in this file" % n)
    return fails


def expand(repo, targets):
    """A target may be a module or a directory; directories walk recursively."""
    out = []
    for rel in targets:
        path = os.path.join(repo, rel.replace("/", os.sep))
        if os.path.isdir(path):
            for base, _dirs, files in os.walk(path):
                for entry in sorted(files):
                    if entry.endswith(".lean"):
                        out.append(os.path.relpath(os.path.join(base, entry),
                                                   repo).replace(os.sep, "/"))
        else:
            out.append(rel)
    return out


def main(argv):
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    targets = expand(repo, argv[1:] or ["YangMills/OS"])
    bad = 0
    for rel in targets:
        fails = check(repo, rel)
        print("%-46s %s" % (rel, "OK" if not fails else "FAIL"))
        for f in fails:
            print("    " + f)
        bad += len(fails)
    print()
    print("modules checked:", len(targets), " failures:", bad)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
