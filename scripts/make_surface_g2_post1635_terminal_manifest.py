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
    specs = (
        ("post1635_0", "surface_scaled_bulk_post1635_terminal_0.txt",
         "surface_scaled_bulk_post1635_terminal_0_rerun.txt"),
        ("post1635_1", "surface_scaled_bulk_post1635_terminal_1.txt",
         "surface_scaled_bulk_post1635_terminal_1_rerun.txt"),
        ("post1635_2_wide", "surface_scaled_bulk_post1635_terminal_2_wide.txt",
         "surface_scaled_bulk_post1635_terminal_2_wide_rerun.txt"),
        ("post1635_3_half", "surface_scaled_bulk_post1635_terminal_3_half.txt",
         "surface_scaled_bulk_post1635_terminal_3_half_rerun.txt"),
    )
    units = []
    for name, production_name, replay_name in specs:
        production = ROOT / "scripts" / production_name
        replay = ROOT / "scripts" / replay_name
        assert production.read_bytes() == replay.read_bytes()
        lines = production.read_text(encoding="utf-8").splitlines()
        beta = next(x.split() for x in lines if x.startswith("beta_domain "))
        rows = sum(x.startswith("trow ") for x in lines)
        units.append({
            "name": name,
            "beta_domain": [beta[1], beta[2]],
            "t_rows": rows,
            "production": {"path": str(production.relative_to(ROOT)).replace("\\", "/"), "sha256": sha(production)},
            "replay": {"path": str(replay.relative_to(ROOT)).replace("\\", "/"), "sha256": sha(replay)},
        })
    for left, right in zip(units, units[1:]):
        assert left["beta_domain"][1] == right["beta_domain"][0]
    manifest = {
        "schema_version": 1,
        "run_id": "surface-scaled-bulk-cwin3p2-post1635-terminal-20260725",
        "claim_scope": "CWIN=3/2 terminal direct-sign cover for beta [1635/16,3297/32]; post1635 extension only; no H_tail/G2/G6 promotion.",
        "status": "terminal_direct_sign_certified",
        "promotion": "NONE",
        "beta_union": [units[0]["beta_domain"][0], units[-1]["beta_domain"][1]],
        "configuration": {"cwin": "3/2", "beta_order": 40,
                          "t_order": 50, "precision": 300,
                          "min_dt": "1/100000"},
        "units": units,
        "total_t_rows": sum(x["t_rows"] for x in units),
        "validator": {"path": "scripts/validate_surface_g2_post1635_terminal.py", "verdict": "PASS"},
    }
    OUT.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print("WROTE", OUT.relative_to(ROOT), "units", len(units),
          "rows", manifest["total_t_rows"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
