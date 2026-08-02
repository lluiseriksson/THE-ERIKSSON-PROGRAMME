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
from lean_decls import declaration_lines   # ONE grammar, self-tested

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TEX = os.path.join(REPO, "papers", "spatial-reconstruction",
                   "spatial_reconstruction.tex")
ORACLE = os.path.join(REPO, "oracle_check.lean")

MODULES = {
    "SpatialOS": os.path.join(REPO, "YangMills", "OS", "SpatialOS.lean"),
    "SpatialReconstruction": os.path.join(REPO, "YangMills", "OS",
                                          "SpatialReconstruction.lean"),
}

# token -> (module, declaration)
LINKS = {
    "SITEBIJLINE": ("SpatialOS", "sum_pathsAt_eq"),
    "PASTJOINLINE": ("SpatialOS", "pastSiteOf_joinSite"),
    "FUTJOINLINE": ("SpatialOS", "futSiteOf_joinSite"),
    "GWJOINLINE": ("SpatialOS", "gibbsWeight_joinSite"),
    "PRODWLINE": ("SpatialOS", "prod_w_joinSite"),
    "PRODKLINE": ("SpatialOS", "prod_K_joinSite"),
    "SITEBRIDGELINE": ("SpatialOS", "osPairingSiteCross_eq_gibbsSum"),
    "SITEDIAGLINE": ("SpatialOS", "osPairingSite_eq_gibbsSum"),
    "SITENNLINE": ("SpatialOS", "gibbsSumSite_reflected_nonneg"),
    "SITEGRAMLINE": ("SpatialOS", "gibbsSumSite_reflected_gram_nonneg"),
    "BONDCROSSLINE": ("SpatialOS", "osPairingBondCross_eq_gibbsSum"),
    "SITECOLLLINE": ("SpatialReconstruction", "siteForm_collapse"),
    "BONDCOLLLINE": ("SpatialReconstruction", "bondForm_collapse"),
    "STARLINE": ("SpatialReconstruction", "siteForm_transferOp"),
    "STARLEFTLINE": ("SpatialReconstruction", "siteForm_transferOp_left"),
    "SALINE": ("SpatialReconstruction", "transferOp_selfAdjoint"),
    "POSLINE": ("SpatialReconstruction", "transferOp_nonneg"),
    "SITENNVEC": ("SpatialReconstruction", "siteForm_self_nonneg"),
    "SURJLINE": ("SpatialReconstruction", "collapse_surjective"),
    "CONSTLINE": ("SpatialReconstruction", "const_mem_halvesAt"),
    "MEASLINE": ("SpatialReconstruction", "osPairing_transfer"),
    "MEASSUMLINE": ("SpatialReconstruction", "osPairing_transfer_gibbsSum"),
}

HEX40 = re.compile(r"[0-9a-fA-F]{40}")


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

    # ---- 2. the permalink line numbers
    for token, (mod, decl) in sorted(LINKS.items()):
        found = lines[mod].get(decl)
        checks.append(("declaration exists: %s.%s" % (mod, decl),
                       found is not None))
        if found is None:
            continue
        before = tex.count("{%s}" % token)
        tex = tex.replace("{%s}" % token, "{%d}" % found)
        checks.append(("token substituted: %s" % token, before >= 1))

    # ---- 3. the counters
    decls_os = len(lines["SpatialOS"])
    decls_rec = len(lines["SpatialReconstruction"])
    oracle_text = io.open(ORACLE, encoding="utf-8", newline="").read()
    cited = set(re.findall(r"#print axioms YangMills\.OS\.([A-Za-z0-9_']+)",
                           oracle_text))
    in_oracle_os = sum(1 for d in lines["SpatialOS"] if d in cited)
    in_oracle = sum(1 for d in lines["SpatialReconstruction"] if d in cited)
    counters = {
        "JOBSAFTER": meas["jobs_after"],
        "JOBSBEFORE": meas["jobs_before"],
        "ORACLETOTAL": meas["oracle_reports"],
        "ORACLENONSTD": meas["oracle_nonstandard"],
        "SORRYCOUNT": meas["sorry_count"],
        "DECLSOS": decls_os,
        "DECLSREC": decls_rec,
        "DECLSINORACLE": in_oracle,
    }
    for token, value in counters.items():
        before = tex.count(token)
        tex = tex.replace(token, str(value))
        checks.append(("counter substituted: %s" % token, before >= 1))

    # the delta the runner predicted BEFORE measuring
    checks.append(("job delta is exactly +1",
                   meas["jobs_after"] - meas["jobs_before"] == 1))
    # BOTH modules, as two independent quantities.  v1.0's check covered only
    # the new module, and the declarations that were actually missing were in
    # the OTHER one.
    checks.append(("every declaration of SpatialReconstruction is in the oracle",
                   in_oracle == decls_rec))
    checks.append(("every declaration of SpatialOS is in the oracle",
                   in_oracle_os == decls_os))
    checks.append(("no non-standard axiom", meas["oracle_nonstandard"] == 0))
    checks.append(("no sorryAx", meas["sorry_count"] == 0))
    checks.append(("no placeholder token survives",
                   not re.search(r"[A-Z]{4,}LINE|PLACEHOLDER", tex)))

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
    print("permalinks  : %d" % len(LINKS))
    print("declarations: SpatialOS %d (%d in oracle), "
          "SpatialReconstruction %d (%d in oracle)"
          % (decls_os, in_oracle_os, decls_rec, in_oracle))
    print("jobs        : %d -> %d (delta %+d)"
          % (meas["jobs_before"], meas["jobs_after"],
             meas["jobs_after"] - meas["jobs_before"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
