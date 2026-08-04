"""Read an oracle log and report its counters, correctly.

WHY THIS EXISTS.  The first attempt counted "non-standard axioms" as the lines
NOT containing the string `propext, Classical.choice, Quot.sound`, and got 1232
out of 2855.  That number is meaningless: a declaration depending on FEWER
axioms --- only `propext, Quot.sound`, or none at all --- fails that test while
being perfectly clean.  The question is never "does this line read like the
standard triple", it is "is any axiom here OUTSIDE the standard set".

So this parses the axiom list of every report and takes the UNION.  A single
name outside `{propext, Classical.choice, Quot.sound}` anywhere is a failure,
and `sorryAx` is reported separately because it is the one that matters most.

Prints JSON on stdout, so the manuscript's counters are read from a process
rather than from a screenshot.  Exit 1 if anything non-standard is present.
No acceptance decision depends on `assert`.

    python scripts/oracle_counters.py <oracle.log> [<core-build.log>]
"""
import io
import json
import re
import sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
JOBS = re.compile(r"\((\d+)\s+jobs?\)")


def main():
    if len(sys.argv) < 2:
        print("usage: oracle_counters.py <oracle.log> [<core-build.log>]")
        return 2
    text = io.open(sys.argv[1], encoding="utf-8", errors="replace").read()
    lines = text.splitlines()

    with_axioms = [l for l in lines if "depends on axioms" in l]
    axiom_free = [l for l in lines if "does not depend on any axioms" in l]
    axioms = set()
    for l in with_axioms:
        body = l.split("axioms:", 1)[1].strip()
        body = body.strip("[]")
        for tok in body.split(","):
            tok = tok.strip()
            if tok:
                axioms.add(tok)
    nonstandard = sorted(a for a in axioms if a not in STANDARD)
    sorry_count = sum(1 for l in lines if "sorryAx" in l)

    out = {
        "oracle_reports": len(with_axioms) + len(axiom_free),
        "oracle_with_axioms": len(with_axioms),
        "oracle_axiom_free": len(axiom_free),
        "oracle_distinct_axioms": sorted(axioms),
        "oracle_nonstandard": len(nonstandard),
        "oracle_nonstandard_names": nonstandard,
        "sorry_count": sorry_count,
    }

    if len(sys.argv) > 2:
        core = io.open(sys.argv[2], encoding="utf-8", errors="replace").read()
        hits = JOBS.findall(core)
        out["jobs"] = int(hits[-1]) if hits else None
        out["core_errors"] = core.count("error:")

    print(json.dumps(out, indent=2, sort_keys=True))
    bad = (nonstandard != []) or sorry_count != 0
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
