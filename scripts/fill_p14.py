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
import hashlib
import io
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_decls import declaration_lines   # ONE traversal, self-tested
from check_no_control_bytes import offenders_bytes   # ONE rule, self-tested


REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TEX = os.path.join(REPO, "papers", "spatial-reconstruction",
                   "spatial_reconstruction.tex")
ORACLE = os.path.join(REPO, "oracle_check.lean")


def sha256_file(path):
    h = hashlib.sha256()
    with io.open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def git_head():
    r = subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPO,
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


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

# THE ANCHOR IS RECOGNISED BY ITS SYNTACTIC FUNCTION, NOT BY ITS SHAPE.  The
# first version matched any 40-hex string, which was fine until the manuscript
# acquired a provenance paragraph quoting two BLOB hashes: it would have
# overwritten the very digests that certify the pre-registration, and then its
# own "exactly one anchor" check would have failed against three matches.  The
# filler is fail-closed, so nothing would have been corrupted --- but nothing
# would ever have been published either.  A rewriter keyed on a lexical form
# cannot tell an anchor from a citation; one keyed on `\newcommand{\anchor}{}`
# can.
ANCHOR_DEF = re.compile(r"(\\newcommand\{\\anchor\}\{)"
                        r"(?P<sha>[0-9a-fA-F]{40})(\})")
HEX40 = re.compile(r"[0-9a-fA-F]{40}")

# Registered in commit 6e67629a, BEFORE any v2 count existed: everything since
# the v1.0 anchor adds declarations to EXISTING modules and adds no module and
# no import, so the core must come back UNCHANGED at the v1.0 absolute.
REGISTERED_JOBS_ABSOLUTE = 8469
REGISTERED_JOBS_DELTA = 0

# The two blob digests the manuscript cites to certify the pre-registration.
# They are NOT the anchor and must survive the anchor rewrite untouched; the
# check that they do is what stops a shape-keyed rewriter from eating them.
PREREG_BLOBS = ["bcfb0363edef76aa6873e057ad2081f2e11bebeb",
                "3e236e54d38dd263730bbedea368fbe232616428"]

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

    # EVERY KEY THE RUN NEEDS, VALIDATED BEFORE ANY OF THEM IS USED.  Feeding
    # the previous version an out-of-date measurements file made it die with a
    # KeyError deep inside the cell table --- a crash, not a checked refusal,
    # and a crash prints no verdict and can be swallowed by a pipe.  A missing
    # key is now a FAILED CHECK like any other.
    required = ["anchor", "baseline_anchor", "jobs_before", "jobs_after",
                "jobs_campaign_base", "core_errors", "oracle_reports",
                "oracle_nonstandard", "sorry_count", "sha256_SpatialOS",
                "sha256_SpatialReconstruction", "sha256_oracle_check"]
    missing = [k for k in required if k not in meas]
    if missing:
        print("measurements file is missing required keys: %s"
              % ", ".join(missing))
        print("manuscript NOT written")
        return 2

    lines = {name: declaration_lines(path) for name, path in MODULES.items()}
    tex = io.open(TEX, encoding="utf-8", newline="").read()

    checks = []          # (name, ok)

    # ---- 1. the anchor, by its DEFINITION and not by its shape
    defs_before = ANCHOR_DEF.findall(tex)
    checks.append(("exactly one anchor definition", len(defs_before) == 1))
    old_anchor = defs_before[0][1].lower() if defs_before else None
    tex, replaced = ANCHOR_DEF.subn(
        lambda m: m.group(1) + anchor + m.group(3), tex, count=1)
    checks.append(("anchor definition rewritten exactly once", replaced == 1))
    checks.append(("anchor present after rewrite",
                   ("\\newcommand{\\anchor}{%s}" % anchor) in tex))
    checks.append(("no stale anchor survives in a definition",
                   all(sha.lower() == anchor
                       for _h, sha, _t in ANCHOR_DEF.findall(tex))))
    # The citation hashes are LEFT ALONE on purpose, and that is checked: they
    # are the pre-registration's certificate, not the anchor.
    others = [h.lower() for h in HEX40.findall(tex)
              if h.lower() not in (anchor, old_anchor)]
    checks.append(("pre-registration blob citations survive untouched",
                   sorted(set(others)) == sorted(set(PREREG_BLOBS))))

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

    # ---- 6. no control bytes, using THE guard's own traversal.  The first
    # version of this block carried its own copy of the rule and dropped EVERY
    # carriage return instead of only the ones followed by a newline, so the
    # standalone guard refused a lone CR and the publisher accepted it --- the
    # exact corruption that produced this guard could have gone straight back
    # into the manuscript.  Two semantics for one rule, a third time.
    checks.append(("no forbidden control bytes in the manuscript",
                   offenders_bytes(tex.encode("utf-8")) == []))

    # ---- 7. THE MEASUREMENT MUST BELONG TO THE ANCHOR.  Without this the
    # filler will happily dress a new tree in an old tree's numbers whenever
    # the numbers happen to agree --- and they agree by construction here,
    # because adding theorems to existing modules leaves the job count alone.
    # This is not hypothetical: the committed measurements file still pointed
    # at the v1.0 anchor while the working tree had moved on twice.
    head = git_head()
    checks.append(("working-tree HEAD is the requested anchor",
                   head is not None and head.lower() == anchor))
    checks.append(("measurement declares the requested anchor",
                   str(meas.get("anchor", "")).lower() == anchor))
    for key, path in (("sha256_SpatialOS", MODULES["SpatialOS"]),
                      ("sha256_SpatialReconstruction",
                       MODULES["SpatialReconstruction"]),
                      ("sha256_oracle_check", ORACLE)):
        checks.append(("measurement hash matches the file: %s" % key,
                       sha256_file(path) == meas.get(key)))
    checks.append(("baseline carries its own identity",
                   str(meas.get("baseline_anchor", "")).strip() != ""))

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
