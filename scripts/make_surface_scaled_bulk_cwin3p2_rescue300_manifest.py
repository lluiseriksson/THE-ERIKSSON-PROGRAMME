"""Create a scoped rescue300 manifest only after independent validation."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--prereg", required=True)
    args = parser.parse_args()
    subprocess.run(
        ["python", "scripts/validate_surface_scaled_bulk_cwin3p2_rescue300.py",
         "--unit", args.unit, "--lo", args.lo, "--hi", args.hi],
        cwd=ROOT, check=True)
    prod = ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}.txt"
    replay = ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}_rerun.txt"
    assert prod.read_bytes() == replay.read_bytes()
    prereg = ROOT / args.prereg
    dependencies = (
        args.prereg,
        "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_rescue300.py",
        "scripts/run_surface_scaled_bulk_cwin3p2_rescue300.py",
        "scripts/validate_surface_scaled_bulk_cwin3p2_rescue300.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
    )
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    manifest = {
        "schema_version": 1,
        "run_id": f"surface-scaled-bulk-cwin3p2-rescue300-{args.tag}-20260726",
        "claim_scope": (f"Candidate-only paired production/replay sign rows on "
                         f"beta [{args.lo},{args.hi}]; strict negativity and t "
                         "adjacency only; no G2, H_tail, K2, K4, or G6 promotion."),
        "status": "current-candidate",
        "git_head": head,
        "command": ["python", "scripts/run_surface_scaled_bulk_cwin3p2_rescue300.py",
                     "--unit", args.unit, "--lo", args.lo, "--hi", args.hi],
        "preregistration": {"path": args.prereg, "sha256": sha256(prereg)},
        "outputs": {"production": {"path": str(prod.relative_to(ROOT)).replace("\\", "/"), "sha256": sha256(prod)},
                    "replay": {"path": str(replay.relative_to(ROOT)).replace("\\", "/"), "sha256": sha256(replay)}},
        "dependencies": {path: sha256(ROOT / path) for path in dependencies},
        "result": {"production_replay_byte_equal": True,
                   "validator": f"CWIN3P2 RESCUE300 VALIDATION PASS {args.unit}",
                   "promotion": "NONE"},
    }
    out = ROOT / "run-records" / "local-staging" / (
        f"surface-scaled-bulk-cwin3p2-rescue300-{args.tag}-20260726.json")
    out.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(out.relative_to(ROOT))

