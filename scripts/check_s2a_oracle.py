"""Reconcile the S-2a oracle output against the module's declarations, BY NAME.

Two house rules are built in rather than assumed:

  * Reconciliation is per DECLARATION, never per LINE.  Lean wraps a long axiom
    list across several lines, and a per-line substring check silently stops
    seeing a declaration when its name grows -- that is ghost #26/#27 in the
    acta, and it cost a false count once already.  The whole output is
    whitespace-normalised into one string and then split into records.

  * No acceptance depends on `assert`.  `python -O` removes assertions, and two
    repository certifiers once emitted a false PASS that way.  Every check here
    raises or returns non-zero in both normal and optimized mode, and PASS is
    printed only after an explicit counter matches the expected total.

  * Comments and docstrings are STRIPPED before any declaration is extracted.
    Prose wraps, and a wrapped sentence can begin a line with "lemma in the list
    closes it" or "lemma applies."  A raw `^(theorem|lemma|def)` scan reads both
    as declarations and then reports them missing from the oracle -- which is
    ghost #26, an oracle list that could not tell code from prose.  Measured
    again here on the bridge module: 37 "declarations" of which 2 were English.

  * The GENERATOR and the CHECKER share this one parser (`--list`).  If the
    script that decides what to interrogate and the script that decides what was
    covered disagree about what a declaration is, the gap between them is
    invisible by construction.

Usage:  check_s2a_oracle.py <module.lean> <oracle-output.txt>
        check_s2a_oracle.py --list <module.lean>
"""

import re
import sys

ALLOWED = {
    "[propext, Classical.choice, Quot.sound]",
    "",  # a plain definition depends on no axioms at all
}

DECL_RE = re.compile(r"^(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)",
                     re.MULTILINE)


def strip_comments(text):
    """Remove Lean block comments (nestable, docstrings included) and `--` lines.

    Replaces removed characters with spaces rather than deleting them, so that
    line structure -- and therefore the `^` anchor in DECL_RE -- is preserved.
    """
    out = list(text)
    i, depth, n = 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if text.startswith("-/", i) and depth > 0:
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0:
            if text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


def declarations(source_path):
    with open(source_path, encoding="utf-8") as handle:
        return DECL_RE.findall(strip_comments(handle.read()))


def verdicts(oracle_path):
    """name -> normalised axiom list ('' when it depends on none)."""
    with open(oracle_path, encoding="utf-8") as handle:
        flat = " ".join(handle.read().split())
    found = {}
    for match in re.finditer(r"'([^']+)'\s+(depends on axioms:\s*(\[[^\]]*\])"
                             r"|does not depend on any axioms)", flat):
        name = match.group(1)
        found[name.split(".")[-1]] = match.group(3) if match.group(3) else ""
    return found


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--list":
        names = declarations(sys.argv[2])
        if not names:
            sys.stderr.write("FAIL: no declarations found in the module\n")
            return 1
        for name in names:
            print(name)
        return 0

    if len(sys.argv) != 3:
        sys.stderr.write("usage: check_s2a_oracle.py <module.lean> <oracle.txt>\n"
                         "       check_s2a_oracle.py --list <module.lean>\n")
        return 2

    expected = declarations(sys.argv[1])
    got = verdicts(sys.argv[2])

    if not expected:
        sys.stderr.write("FAIL: no declarations found in the module\n")
        return 1

    accepted = 0
    failures = []
    for name in expected:
        if name not in got:
            failures.append("%s: NO ORACLE RECORD" % name)
            continue
        axioms = got[name]
        if axioms not in ALLOWED:
            failures.append("%s: nonstandard axioms %s" % (name, axioms))
            continue
        accepted += 1
        print("  ok  %-24s %s" % (name, axioms if axioms else "(no axioms)"))

    orphans = sorted(set(got) - set(expected))
    for name in orphans:
        failures.append("%s: oracle record with no declaration in the module" % name)

    for line in failures:
        sys.stderr.write("FAIL: %s\n" % line)

    print("declarations expected: %d" % len(expected))
    print("declarations accepted: %d" % accepted)

    if failures:
        return 1
    if accepted != len(expected):
        sys.stderr.write("FAIL: counter %d does not match expected %d\n"
                         % (accepted, len(expected)))
        return 1
    print("PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
