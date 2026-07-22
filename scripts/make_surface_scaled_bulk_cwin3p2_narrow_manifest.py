"""Manifest the preregistered narrow CWIN=3/2 candidate descendants."""

from datetime import datetime, timezone
import argparse
import hashlib
import json
from fractions import Fraction
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
    parser.add_argument("--index", type=int, required=True)
    parser.add_argument("--base", choices=("69", "69.5", "70", "71", "72", "73"), default="69.5")
    args = parser.parse_args()
    index = args.index
    base = Fraction(139, 2) if args.base == "69.5" else Fraction(int(args.base))
    count = 8 if args.base in {"69", "69.5", "72", "73"} else 16
    if not 0 <= index < count:
        raise SystemExit(f"index must lie in [0,{count}) for base {args.base}")
    if args.base in {"69", "69.5"}:
        unit = f"cwin3p2_{index:02d}" if args.base == "69" else f"cwin3p2_69p5_{index:02d}"
        prereg = "SURFACE-SCALED-BULK-CWIN3P2-NARROW-PREREG.md"
    else:
        unit = f"cwin3p2_{args.base}_{index:02d}"
        prereg = f"SURFACE-SCALED-BULK-CWIN3P2-{args.base}-{int(args.base)+1}-PREREG.md"
    step_den = 8 if args.base in {"72", "73"} else 16
    lo_value = base + Fraction(index, step_den)
    hi_value = lo_value + Fraction(1, step_den)
    lo = str(lo_value)
    hi = str(hi_value)
    if args.base == "69":
        validator = "validate_surface_scaled_bulk_cwin3p2_narrow_69_69p5.py"
    elif args.base == "69.5":
        validator = "validate_surface_scaled_bulk_cwin3p2_69p5_70.py"
    else:
        validator = f"validate_surface_scaled_bulk_cwin3p2_{args.base.replace('.', 'p')}_{int(args.base)+1}.py"
    outputs = [
        artifact(f"scripts/surface_scaled_bulk_{unit}.txt"),
        artifact(f"scripts/surface_scaled_bulk_{unit}_rerun.txt"),
    ]
    inputs = [
        artifact("docs/" + prereg),
        artifact("scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_narrow.py"),
        artifact("scripts/certify_bulk_beta_taylor_scaled_design.py"),
        artifact("scripts/certify_bulk_beta_taylor_arb.py"),
        artifact("scripts/" + validator),
    ]
    now = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")
    data = {
        "schema_version": 1,
        "run_id": f"surface-scaled-bulk-cwin3p2-narrow-{unit}-20260722",
        "claim_scope": (
            f"Candidate-only paired production/replay for beta [{lo},{hi}] "
            "with CWIN=3/2, order-24/t-order-29 rows. Sign rows do not imply "
            "H_tail; no G2/G6 promotion."
        ),
        "status": "current",
        "started_utc": now,
        "finished_utc": now,
        "command": [
            "python", "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_narrow.py",
            "--unit", unit, "--lo", lo, "--hi", hi,
        ],
        "working_directory": ".",
        "environment": {"python": "3.12.6", "libraries": {"python-flint": "0.9.0"}},
        "inputs": inputs,
        "outputs": outputs,
        "supersedes": [],
        "superseded_by": None,
        "quarantine_reason": None,
    }
    out = ROOT / "run-manifests" / f"{data['run_id']}.json"
    out.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print("WROTE", out.relative_to(ROOT))


if __name__ == "__main__":
    main()
