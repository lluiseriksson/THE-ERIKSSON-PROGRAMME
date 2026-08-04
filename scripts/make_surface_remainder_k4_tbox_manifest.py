"""Create a scoped K4 t-box manifest after its validator has passed."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/surface_remainder_centered_delta_integrator_design.py",
    "scripts/surface_remainder_centered_delta_carrier.py",
    "scripts/surface_remainder_complement_l3_smoke.py",
    "scripts/surface_remainder_tjet.py",
    "scripts/surface_remainder_complement.py",
    "scripts/surface_bessel_integral_remainder.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--t-lo", required=True)
    parser.add_argument("--t-hi", required=True)
    args = parser.parse_args()
    prod = ROOT / "scripts" / f"surface_remainder_k4_tbox_{args.unit}.txt"
    replay = ROOT / "scripts" / f"surface_remainder_k4_tbox_{args.unit}_rerun.txt"
    driver = ROOT / "scripts" / "run_surface_remainder_k4_tbox_endpoint.py"
    validator = ROOT / "scripts" / "validate_surface_remainder_k4_tbox_endpoint.py"
    # Refuse to create a manifest for a transcript that has not passed the
    # exact production/replay validator.
    subprocess.run(
        ["python", "scripts/validate_surface_remainder_k4_tbox_endpoint.py",
         "--unit", args.unit, "--t-lo", args.t_lo, "--t-hi", args.t_hi],
        cwd=ROOT, check=True)
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    manifest = {
        "schema_version": 1,
        "run_id": f"surface-remainder-k4-tbox-{args.unit}-20260726",
        "status": "CERTIFIED_SCOPED_WITNESS",
        "claim_scope": (
            f"Current-hash K4 endpoint t-box [{args.t_lo},{args.t_hi}], "
            "delta=[0.048,0.05]; two adjacent boxes, seven aggregate budget "
            "fractions with strict outward upper endpoint < 1. This is not a "
            "global K4 or S1'''/S2''' certificate."),
        "git_head": head,
        "transcripts": {
            "production": {"path": str(prod.relative_to(ROOT)).replace("\\", "/"),
                            "sha256": sha256(prod)},
            "replay": {"path": str(replay.relative_to(ROOT)).replace("\\", "/"),
                        "sha256": sha256(replay)},
        },
        "driver": {"path": "scripts/run_surface_remainder_k4_tbox_endpoint.py",
                    "sha256": sha256(driver)},
        "validator": {"path": "scripts/validate_surface_remainder_k4_tbox_endpoint.py",
                       "sha256": sha256(validator)},
        "dependencies": {p: sha256(ROOT / p) for p in DEPENDENCIES},
        "result": {"segments": 2, "delta_domain": ["0.048", "0.05"],
                   "t_domain": [args.t_lo, args.t_hi],
                   "production_replay_byte_equal": True,
                   "all_seven_totals_strictly_below_one": True,
                   "validator": f"K4 GENERIC TBOX VALIDATION PASS {args.unit}"},
        "promotion": "NONE",
    }
    out = ROOT / "run-manifests" / (
        f"surface-remainder-k4-tbox-{args.unit}-20260726.json")
    out.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(out.relative_to(ROOT))


if __name__ == "__main__":
    main()
