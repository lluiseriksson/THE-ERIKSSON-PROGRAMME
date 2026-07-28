"""Audit the finite-beta W-sign candidate archive under the exact direct relay.

This is deliberately a read-only diagnostic.  It does not promote manifests or
change G2/G6.  Unlike ``audit_surface_g2_relay_admissibility.py`` it includes
quarantined candidate manifests, because the direct algebraic relay

    W = 4 F_B^2 E',   W^J = s^8 W,   s > 0

can make their strict W-sign rows relevant once their provenance and coverage
are independently checked.  The report separates terminal/current units from
quarantined units and reports any beta gaps in both unions.
"""

from __future__ import annotations

import json
import subprocess
from fractions import Fraction
from pathlib import Path

from flint import ctx

from audit_surface_g2_relay_admissibility import (
    BETA_HI,
    BETA_LO,
    ROOT,
    output_groups,
    parse_transcript,
    verify_outputs,
)
from run_record_archive import iter_auditable_run_records


def beta_union(units):
    boxes = sorted(
        (Fraction(u["transcript"]["beta"][0]),
         Fraction(u["transcript"]["beta"][1]))
        for u in units if u["ok"]
    )
    gaps = []
    if boxes and boxes[0][0] > BETA_LO:
        gaps.append([str(BETA_LO), str(boxes[0][0])])
    for left, right in zip(boxes, boxes[1:]):
        if left[1] < right[0]:
            gaps.append([str(left[1]), str(right[0])])
    if boxes and boxes[-1][1] < BETA_HI:
        gaps.append([str(boxes[-1][1]), str(BETA_HI)])
    complete = bool(
        boxes and boxes[0][0] == BETA_LO and boxes[-1][1] == BETA_HI
        and all(a[1] == b[0] for a, b in zip(boxes, boxes[1:]))
    )
    return boxes, gaps, complete


def scan():
    units = []
    for _, path in iter_auditable_run_records("surface-scaled-bulk-*.json"):
        try:
            manifest = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        claim = str(manifest.get("claim_scope", ""))
        run_id = str(manifest.get("run_id", ""))
        if "CWIN=3/2" not in claim and "cwin3p2" not in run_id:
            continue
        for group_name, production, replay in output_groups(manifest):
            reasons = verify_outputs(production, replay)
            pp = ROOT / production["path"]
            parsed = parse_transcript(pp) if pp.is_file() else {
                "ok": False, "reasons": ["no_production_transcript"]
            }
            reasons.extend(parsed.get("reasons", []))
            units.append({
                "manifest": path.name,
                "unit": group_name,
                "status": str(manifest.get("status", "")),
                "ok": not reasons and parsed.get("ok", False),
                "reasons": sorted(set(reasons)),
                "transcript": parsed,
            })
    return units


def main():
    ctx.prec = 180
    relay = subprocess.run(
        ["python", "scripts/verify_surface_direct_sign_relay.py"],
        cwd=ROOT, text=True, capture_output=True, check=False,
    )
    units = scan()
    terminal = [u for u in units if u["ok"] and u["status"].lower()
                not in {"quarantined", "quarantined-candidate-only",
                        "design_only", "design-only"}]
    candidate = [u for u in units if u["ok"] and u["status"].lower()
                 in {"quarantined", "quarantined-candidate-only",
                     "design_only", "design-only"}]
    all_ok = terminal + candidate
    _, terminal_gaps, terminal_complete = beta_union(terminal)
    boxes, candidate_gaps, candidate_complete = beta_union(all_ok)
    out = {
        "relay_algebra_exit": relay.returncode,
        "relay_algebra_pass": relay.returncode == 0,
        "units_seen": len(units),
        "terminal_units": len(terminal),
        "candidate_units": len(candidate),
        "terminal_beta_complete": terminal_complete,
        "terminal_beta_gaps": terminal_gaps,
        "all_verified_beta_complete": candidate_complete,
        "all_verified_beta_gaps": candidate_gaps,
        "all_verified_boxes": [[str(a), str(b)] for a, b in boxes],
        "candidate_failures": [
            {"manifest": u["manifest"], "unit": u["unit"],
             "status": u["status"], "reasons": u["reasons"]}
            for u in units if not u["ok"]
        ],
        "promotion": "NONE_READ_ONLY",
    }
    print(json.dumps(out, indent=2, sort_keys=True))
    print("DIRECT-SIGN CANDIDATE UNION AUDIT ONLY; NO G2/G6 PROMOTION")


if __name__ == "__main__":
    raise SystemExit(main())
