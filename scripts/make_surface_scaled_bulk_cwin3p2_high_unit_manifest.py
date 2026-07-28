"""Create a candidate manifest for one preregistered high-order unit."""

from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def artifact(relative: str) -> dict:
    path = ROOT / relative
    raw = path.read_bytes()
    return {
        "path": relative,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "sha256_lf": hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--prereg", required=True)
    args = parser.parse_args()
    prefix = f"scripts/surface_scaled_bulk_{args.unit}"
    outputs = [artifact(prefix + suffix + ".txt") for suffix in ("", "_rerun")]
    inputs = [
        artifact("docs/" + args.prereg),
        artifact("scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py"),
        artifact("scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py"),
        artifact("scripts/certify_bulk_beta_taylor_scaled_design.py"),
        artifact("scripts/certify_bulk_beta_taylor_arb.py"),
        artifact("scripts/validate_surface_scaled_bulk_cwin3p2_high_unit.py"),
    ]
    now = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")
    data = {
        "schema_version": 1,
        "run_id": args.run_id,
        "claim_scope": (
            f"Candidate-only paired production/replay for beta [{args.lo},{args.hi}] "
            "with CWIN=3/2, order-30/t-order-37 rows. Sign rows do not imply "
            "H_tail; no G2/G6 promotion."
        ),
        "status": "current",
        "started_utc": now,
        "finished_utc": now,
        "command": [
            "python", "scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py",
            "--unit", args.unit, "--lo", args.lo, "--hi", args.hi,
        ],
        "working_directory": ".",
        "environment": {"python": "3.12.6", "libraries": {"python-flint": "0.9.0"}},
        "inputs": inputs,
        "outputs": outputs,
        "supersedes": [],
        "superseded_by": None,
        "quarantine_reason": None,
    }
    out = ROOT / "run-records" / "local-staging" / f"{args.run_id}.json"
    out.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print("WROTE", out.relative_to(ROOT))


if __name__ == "__main__":
    main()
