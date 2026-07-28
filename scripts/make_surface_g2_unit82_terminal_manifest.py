"""Freeze hashes for the fresh three-slice terminal direct-sign run."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "run-manifests" / "surface-scaled-bulk-cwin3p2-unit82-terminal-20260725.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unit(name: str, lo: str, hi: str, rows: int) -> dict:
    production = ROOT / "scripts" / f"surface_scaled_bulk_unit82_rescue_order30{name}.txt"
    replay = ROOT / "scripts" / f"surface_scaled_bulk_unit82_rescue_order30{name}_rerun.txt"
    digest = sha(production)
    assert production.read_bytes() == replay.read_bytes()
    return {
        "name": name or "slice1",
        "beta_domain": [lo, hi],
        "t_rows": rows,
        "production": {"path": str(production.relative_to(ROOT)).replace("\\", "/"),
                        "sha256": digest},
        "replay": {"path": str(replay.relative_to(ROOT)).replace("\\", "/"),
                    "sha256": digest},
    }


def main() -> int:
    units = [
        unit("", "275/4", "1101/16", 167),
        unit("_slice2", "1101/16", "1103/16", 172),
        unit("_slice3", "1103/16", "69", 167),
    ]
    manifest = {
        "schema_version": 1,
        "run_id": "surface-scaled-bulk-cwin3p2-unit82-terminal-20260725",
        "claim_scope": "CWIN=3/2 terminal direct-sign cover for beta [275/4,69]; no H_tail/G2/G6 promotion.",
        "status": "terminal_direct_sign_certified",
        "promotion": "NONE",
        "beta_union": ["275/4", "69"],
        "configuration": {"cwin": "3/2", "beta_order": 30,
                          "t_order": 35, "precision": 220,
                          "min_dt": "1/100000"},
        "units": units,
        "total_t_rows": sum(x["t_rows"] for x in units),
        "validator": {"path": "scripts/validate_surface_g2_unit82_terminal_manifest.py",
                       "verdict": "PENDING"},
    }
    OUT.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print("WROTE", OUT.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
