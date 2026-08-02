"""Fill paper 14's anchor, permalink lines and counters FROM the repository.

Nothing in the manuscript that a process can derive is typed by hand.  Three
defects in this lane came from typing: a hash tail, a changed-file list, and a
counter row that no script owned and that consequently drifted.

WHY THE ANCHOR IS REWRITTEN BY PATTERN AND NOT BY PLACEHOLDER.  A previous
filler in this lane replaced a literal `ANCHORPLACEHOLDER`, which stops existing
after the first version; from v1.1 onwards it silently kept the old hash while
its own final check passed vacuously.  So this one rewrites whatever 40-hex
string is currently there, and then CHECKS the new one is present and the old
one is gone.  A check that cannot fail is not a check.

WHY THE COUNTERS ARE REWRITTEN BY STABLE MARKER --- the same lesson, learned a
second time and one level down.  v1.0's counters were bare tokens like
`JOBSAFTER`, which also stop existing the moment they are filled, so the filler
could not refill an already-materialised manuscript: it demanded tokens that its
own previous run had consumed.  Each counter row now carries a LaTeX comment
marker `% @@TOKEN@@` at end of line.  The marker survives every version, and the
filler rewrites the CELL on the marked row.

WHY THE PREDICTION IS HARD-CODED HERE AND NOT READ FROM THE MEASUREMENTS.  A
prediction supplied in the same file as the numbers it judges is not a
prediction.  The two values below were registered in commit `6e67629a`, before
any v2 count existed, and BOTH are checked --- the absolute and the delta ---
because the registration made both claims.

No acceptance decision here depends on `assert`: `python -O` deletes those, and
this repository has twice emitted a false PASS that way.  Every check below is
explicit, counted, and exits non-zero in both modes.

Usage:
    python scripts/fill_p14.py <anchor-sha> <measurements.json>
"""
import io
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_decls import declaration_lines   # ONE traversal, self-tested

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TEX = os.path.join(REPO, "papers", "spatial-reconstruction",
                   "spatial_reconstruction.tex")
ORACLE = os.path.join(REPO, "oracle_check.lean")

MODULES = {
    "SpatialOS": os.path.join(REPO, "YangMills", "OS", "SpatialOS.lean"),
    "SpatialReconstruction": os.path.join(REPO, "YangMills", "OS",
                                          "SpatialReconstruction.lean"),
}

# THERE IS NO TOKEN TABLE, AND THAT IS THE POINT.  v1.0 named each permalink by
# a placeholder like `SITEBIJLINE`, which stops existing the moment it is filled
# --- so a second run could not refill an already-materialised manuscript, and a
# table that drifted from the text would go unnoticed.  The stable key is the
# thing that cannot disappear: the DECLARATION NAME, which is already the third
# argument of `\osline`.  The filler rewrites the line-number argument of every
# occurrence, looking the name up in the module.  No table, so nothing to drift.
OSLINE = re.compile(r"\\osline\{(?P<mod>[A-Za-z]+)\}"
                    r"\{(?P<line>[^{}]*)\}\{(?P<name>[^{}]*)\}")

HEX40 = re.compile(r"[0-9a-fA-F]{40}")

# Registered in commit 6e67629a, BEFORE any v2 count existed: everything since
# the v1.0 anchor adds declarations to EXISTING modules and adds no module and
# no import, so the core must come back UNCHANGED at the v1.0 absolute.
REGISTERED_JOBS_ABSOLUTE = 8469
REGISTERED_JOBS_DELTA = 0

ROW = re.compile(r"^(?P<head>.*?&\s*)(?P<cell>.*?)"
                 r"(?P<tail>\s*\\\\\s*%\s*@@(?P<tok>\w+)@@\s*)$")


def main():
    if len(sys.argv) != 3:
        print("usage: fill_p14.py <anchor-sha> <measurements.json>")
        return 2
    anchor = sys.argv[1].strip().lower()
    if HEX40.fullmatch(anchor) is None:
        print("anchor is not a 40-hex sha: %r" % anchor)
        return 2
    with io.open(sys.argv[2], encoding="utf-8") as f:
        meas = json.load(f)

    lines = {name: declaration_lines(path) for name, path in MODULES.items()}
    tex = io.open(TEX, encoding="utf-8", newline="").read()
    old_anchor_hits = HEX40.findall(tex)

    checks = []          # (name, ok)

    # ---- 1. the anchor, by pattern
    tex = HEX40.sub(anchor, tex)
    checks.append(("anchor present after rewrite", anchor in tex))
    stale = [h for h in set(x.lower() for x in old_anchor_hits) if h != anchor]
    checks.append(("no stale anchor survives",
                   all(h not in tex.lower() for h in stale)))
    checks.append(("exactly one anchor definition",
                   len(HEX40.findall(tex)) == 1))

    # ---- 2. the permalink line numbers, keyed by the declaration name itself
    unresolved = []
    resolved = [0]

    def _fix(m):
        mod = m.group("mod")
        decl = m.group("name").replace("\\_", "_")
        found = lines.get(mod, {}).get(decl)
        if found is None:
            unresolved.append("%s.%s" % (mod, decl))
            return m.group(0)
        resolved[0] += 1
        return "\\osline{%s}{%d}{%s}" % (mod, found, m.group("name"))

    tex = OSLINE.sub(_fix, tex)
    checks.append(("every cited declaration resolves: %s"
                   % (", ".join(sorted(set(unresolved))) or "none unresolved"),
                   not unresolved))
    checks.append(("at least one permalink was rewritten", resolved[0] > 0))

    # ---- 3. the counters, by STABLE MARKER
    decls_os = len(lines["SpatialOS"])
    decls_rec = len(lines["SpatialReconstruction"])
    oracle_text = io.open(ORACLE, encoding="utf-8", newline="").read()
    cited = set(re.findall(r"#print axioms YangMills\.OS\.([A-Za-z0-9_']+)",
                           oracle_text))
    in_oracle_os = sum(1 for d in lines["SpatialOS"] if d in cited)
    in_oracle = sum(1 for d in lines["SpatialReconstruction"] if d in cited)
    delta = meas["jobs_after"] - meas["jobs_before"]
    cells = {
        "JOBSAFTER": "%d jobs, success" % meas["jobs_after"],
        "JOBSBEFORE": "%d jobs" % meas["jobs_before"],
        "JOBSDELTA": "$%+d$" % delta,
        "JOBSCAMPAIGNBASE": "%d jobs" % meas["jobs_campaign_base"],
        "ORACLETOTAL": "%d" % meas["oracle_reports"],
        "ORACLENONSTD": "%d" % meas["oracle_nonstandard"],
        "DECLSOS": "%d" % decls_os,
        "DECLSOSORACLE": "%d" % in_oracle_os,
        "DECLSREC": "%d" % decls_rec,
        "DECLSRECORACLE": "%d" % in_oracle,
        "SORRYCOUNT": "%d" % meas["sorry_count"],
        "COREERRORS": "%d" % meas["core_errors"],
    }
    seen = {}
    out_lines = []
    for raw in tex.split("\n"):
        m = ROW.match(raw)
        if m is not None and m.group("tok") in cells:
            tok = m.group("tok")
            seen[tok] = seen.get(tok, 0) + 1
            raw = m.group("head") + cells[tok] + m.group("tail")
        out_lines.append(raw)
    tex = "\n".join(out_lines)
    for tok in sorted(cells):
        checks.append(("counter row marked exactly once: %s" % tok,
                       seen.get(tok, 0) == 1))

    # ---- 4. the prediction registered BEFORE measuring, both halves of it
    checks.append(("core matches the registered absolute (%d)"
                   % REGISTERED_JOBS_ABSOLUTE,
                   meas["jobs_after"] == REGISTERED_JOBS_ABSOLUTE))
    checks.append(("delta matches the registered delta (%+d)"
                   % REGISTERED_JOBS_DELTA, delta == REGISTERED_JOBS_DELTA))

    # ---- 5. coverage, for BOTH modules as independent quantities.  v1.0
    # checked only the new module, and the declarations actually missing were
    # in the OTHER one.
    checks.append(("every declaration of SpatialReconstruction is in the oracle",
                   in_oracle == decls_rec))
    checks.append(("every declaration of SpatialOS is in the oracle",
                   in_oracle_os == decls_os))
    checks.append(("no non-standard axiom", meas["oracle_nonstandard"] == 0))
    checks.append(("no sorryAx", meas["sorry_count"] == 0))
    checks.append(("no permalink placeholder survives",
                   re.search(r"\{[A-Z]{4,}LINE\}|PLACEHOLDER", tex) is None))
    checks.append(("every osline carries a numeric line",
                   all(m.group("line").isdigit()
                       for m in OSLINE.finditer(tex))))
    checks.append(("no counter token survives in a cell",
                   not any(re.search(r"&\s*%s\s*\\\\" % t, tex) for t in cells)))

    ran = 0
    failed = []
    for name, ok in checks:
        ran += 1
        if not ok:
            failed.append(name)
    if ran != len(checks):
        print("check counter disagrees: %d of %d" % (ran, len(checks)))
        return 2
    if failed:
        for name in failed:
            print("FAILED CHECK:", name)
        print("manuscript NOT written")
        return 2

    io.open(TEX, "w", encoding="utf-8", newline="").write(tex)
    print("checks run: %d, all passed" % ran)
    print("anchor      : %s" % anchor)
    print("permalinks  : %d rewritten by declaration name" % resolved[0])
    print("declarations: SpatialOS %d (%d in oracle), "
          "SpatialReconstruction %d (%d in oracle)"
          % (decls_os, in_oracle_os, decls_rec, in_oracle))
    print("jobs        : %d -> %d (delta %+d; registered %+d at absolute %d)"
          % (meas["jobs_before"], meas["jobs_after"], delta,
             REGISTERED_JOBS_DELTA, REGISTERED_JOBS_ABSOLUTE))
    return 0


if __name__ == "__main__":
    sys.exit(main())
