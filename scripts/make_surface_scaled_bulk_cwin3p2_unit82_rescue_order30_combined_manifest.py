"""Write the combined quarantined manifest for all unit-82 rescue slices."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "run-records/local-staging/surface-scaled-bulk-cwin3p2-unit82-rescue-order30-combined-20260723.json"
SLICES = (
    ("slice1", "surface_scaled_bulk_unit82_rescue_order30", "275/4", "1101/16", 167),
    ("slice2", "surface_scaled_bulk_unit82_rescue_order30_slice2", "1101/16", "1103/16", 172),
    ("slice3", "surface_scaled_bulk_unit82_rescue_order30_slice3", "1103/16", "69", 167),
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    units = []
    for label, stem, lo, hi, expected in SLICES:
        prod = ROOT / f"scripts/{stem}.txt"
        replay = ROOT / f"scripts/{stem}_rerun.txt"
        assert prod.read_bytes() == replay.read_bytes()
        rows = sum(line.startswith("trow ") for line in prod.read_text(encoding="utf-8").splitlines())
        assert rows == expected
        units.append({
            "label": label,
            "beta_domain": [lo, hi],
            "rows": rows,
            "production": {"path": str(prod.relative_to(ROOT)), "sha256": sha(prod)},
            "replay": {"path": str(replay.relative_to(ROOT)), "sha256": sha(replay)},
        })
    deps = {}
    for rel in (
        "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30.py",
        "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_continuation.py",
        "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_slice.py",
        "scripts/validate_surface_scaled_bulk_cwin3p2_unit82_rescue_order30.py",
        "scripts/validate_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_continuation.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
    ):
        deps[rel] = {"path": rel, "sha256": sha(ROOT / rel)}
    payload = {
        "schema_version": 1,
        "run_id": "surface-scaled-bulk-cwin3p2-unit82-rescue-order30-combined-20260723",
        "status": "quarantined",
        "claim_scope": "Order-30/35 sign evidence exhausting beta [275/4,69] in three rescue slices; no H_tail/G2/G6 promotion.",
        "config": {"cwin": "3/2", "beta_order": 30, "t_order": 35,
                   "prec": 220, "min_dt": "1/100000"},
        "beta_union": ["275/4", "69"],
        "units": units,
        "total_rows": sum(u["rows"] for u in units),
        "dependencies": deps,
        "validator": {
            "paths": [
                "scripts/validate_surface_scaled_bulk_cwin3p2_unit82_rescue_order30.py",
                "scripts/validate_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_continuation.py",
            ],
            "verdict": "PASS",
            "production_replay_byte_identical": True,
        },
        "promotion": "NONE",
    }
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(OUT)
    print("UNIT82 COMBINED MANIFEST WRITTEN slices", len(units), "rows", payload["total_rows"])


if __name__ == "__main__":
    main()
