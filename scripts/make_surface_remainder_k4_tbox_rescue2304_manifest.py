"""Write a scoped manifest only after the rescue validator passes."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/run_surface_remainder_k4_tbox_rescue2304.py",
    "scripts/run_surface_remainder_k4_tbox_endpoint.py",
    "scripts/validate_surface_remainder_k4_tbox_rescue2304.py",
    "scripts/surface_remainder_centered_delta_integrator_design.py",
    "scripts/surface_remainder_centered_delta_carrier.py",
    "scripts/surface_remainder_complement_l3_smoke.py",
    "scripts/surface_remainder_tjet.py",
    "scripts/surface_remainder_complement.py",
    "scripts/surface_bessel_integral_remainder.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--t-lo", required=True)
    parser.add_argument("--t-hi", required=True)
    args = parser.parse_args()
    subprocess.run(
        ["python", "scripts/validate_surface_remainder_k4_tbox_rescue2304.py",
         "--unit", args.unit, "--t-lo", args.t_lo, "--t-hi", args.t_hi],
        cwd=ROOT, check=True)
    prod = ROOT / "scripts" / f"surface_remainder_k4_tbox_rescue2304_{args.unit}.txt"
    replay = ROOT / "scripts" / f"surface_remainder_k4_tbox_rescue2304_{args.unit}_rerun.txt"
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    manifest = {
        "schema_version": 1,
        "run_id": f"surface-remainder-k4-tbox-rescue2304-{args.unit}-20260726",
        "status": "CERTIFIED_SCOPED_WITNESS",
        "claim_scope": (f"Current-hash K4 endpoint t-box [{args.t_lo},{args.t_hi}], "
                         "delta=[0.048,0.05], two 2,304-cell adjacent boxes; "
                         "not a global K4 or S1'''/S2''' certificate."),
        "git_head": head,
        "transcripts": {"production": {"path": str(prod.relative_to(ROOT)).replace("\\", "/"), "sha256": sha256(prod)},
                        "replay": {"path": str(replay.relative_to(ROOT)).replace("\\", "/"), "sha256": sha256(replay)}},
        "driver": {"path": "scripts/run_surface_remainder_k4_tbox_rescue2304.py",
                    "sha256": sha256(ROOT / "scripts/run_surface_remainder_k4_tbox_rescue2304.py")},
        "validator": {"path": "scripts/validate_surface_remainder_k4_tbox_rescue2304.py",
                       "sha256": sha256(ROOT / "scripts/validate_surface_remainder_k4_tbox_rescue2304.py")},
        "dependencies": {p: sha256(ROOT / p) for p in DEPENDENCIES},
        "result": {"segments": 2, "cells_per_segment": 2304,
                   "delta_domain": ["0.048", "0.05"], "t_domain": [args.t_lo, args.t_hi],
                   "production_replay_byte_equal": True,
                   "all_seven_totals_strictly_below_one": True},
        "promotion": "NONE",
    }
    out = ROOT / "run-records" / "local-staging" / f"surface-remainder-k4-tbox-rescue2304-{args.unit}-20260726.json"
    out.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(out.relative_to(ROOT))

