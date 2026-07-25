"""Freeze the verified first rescue-300 box after 1635/16."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "run-manifests" / "surface-scaled-bulk-cwin3p2-post1635-terminal-20260725.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    production = ROOT / "scripts" / "surface_scaled_bulk_post1635_terminal_0.txt"
    replay = ROOT / "scripts" / "surface_scaled_bulk_post1635_terminal_0_rerun.txt"
    assert production.read_bytes() == replay.read_bytes()
    lines = production.read_text(encoding="utf-8").splitlines()
    beta = next(x.split() for x in lines if x.startswith("beta_domain "))
    rows = sum(x.startswith("trow ") for x in lines)
    manifest = {
        "schema_version": 1,
        "run_id": "surface-scaled-bulk-cwin3p2-post1635-terminal-20260725",
        "claim_scope": "CWIN=3/2 terminal direct-sign cover for beta [1635/16,3271/32]; post1635 extension only; no H_tail/G2/G6 promotion.",
        "status": "terminal_direct_sign_certified",
        "promotion": "NONE",
        "beta_union": [beta[1], beta[2]],
        "configuration": {"cwin": "3/2", "beta_order": 40,
                          "t_order": 50, "precision": 300,
                          "min_dt": "1/100000"},
        "units": [{
            "name": "post1635_0",
            "beta_domain": [beta[1], beta[2]],
            "t_rows": rows,
            "production": {"path": str(production.relative_to(ROOT)).replace("\\", "/"), "sha256": sha(production)},
            "replay": {"path": str(replay.relative_to(ROOT)).replace("\\", "/"), "sha256": sha(replay)},
        }],
        "total_t_rows": rows,
        "validator": {"path": "scripts/validate_surface_g2_post1635_terminal.py", "verdict": "PASS"},
    }
    OUT.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print("WROTE", OUT.relative_to(ROOT), "rows", rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
