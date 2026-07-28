"""Record the paired candidate manifest for the preregistered 74--74.25 box."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "run-records" / "local-staging" / "surface-scaled-bulk-cwin3p2-high-74-74p25-20260721.json"


def artifact(relative: str) -> dict:
    path = ROOT / relative
    raw = path.read_bytes()
    return {
        "path": relative,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "sha256_lf": hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest(),
    }


def main() -> None:
    outputs = [
        artifact("scripts/surface_scaled_bulk_high_74_74p25.txt"),
        artifact("scripts/surface_scaled_bulk_high_74_74p25_rerun.txt"),
    ]
    inputs = [
        artifact("docs/SURFACE-SCALED-BULK-CWIN3P2-HIGH-74-74P25-PREREG.md"),
        artifact("scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py"),
        artifact("scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py"),
        artifact("scripts/certify_bulk_beta_taylor_scaled_design.py"),
        artifact("scripts/certify_bulk_beta_taylor_arb.py"),
        artifact("scripts/validate_surface_scaled_bulk_cwin3p2_high_unit.py"),
    ]
    now = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")
    data = {
        "schema_version": 1,
        "run_id": "surface-scaled-bulk-cwin3p2-high-74-74p25-20260721",
        "claim_scope": (
            "Candidate-only paired production/replay for beta [74,297/4] "
            "with CWIN=3/2, order-30/t-order-37 rows. Sign rows do not "
            "imply H_tail; no G2/G6 promotion."
        ),
        "status": "current",
        "started_utc": now,
        "finished_utc": now,
        "command": [
            "python",
            "scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py",
            "--unit",
            "high_74_74p25",
            "--lo",
            "74",
            "--hi",
            "297/4",
        ],
        "working_directory": ".",
        "environment": {"python": "3.12.6", "libraries": {"python-flint": "0.9.0"}},
        "inputs": inputs,
        "outputs": outputs,
        "supersedes": [],
        "superseded_by": None,
        "quarantine_reason": None,
    }
    OUT.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print("WROTE", OUT.relative_to(ROOT))


if __name__ == "__main__":
    main()
