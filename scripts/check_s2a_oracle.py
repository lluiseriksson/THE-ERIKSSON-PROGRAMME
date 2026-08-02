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

Usage:  check_s2a_oracle.py <module.lean> <oracle-output.txt>
"""

import re
import sys

ALLOWED = {
    "[propext, Classical.choice, Quot.sound]",
    "",  # a plain definition depends on no axioms at all
}

DECL_RE = re.compile(r"^(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)",
                     re.MULTILINE)


def declarations(source_path):
    with open(source_path, encoding="utf-8") as handle:
        return DECL_RE.findall(handle.read())


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
    if len(sys.argv) != 3:
        sys.stderr.write("usage: check_s2a_oracle.py <module.lean> <oracle.txt>\n")
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
