"""Freeze the complete order-24 terminal cover for beta [241/4,275/4]."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from validate_surface_g2_mid24_terminal import validate

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "run-manifests" / "surface-scaled-bulk-cwin3p2-mid24-terminal-20260725.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def make_unit(index: int) -> dict:
    matches = sorted(ROOT.glob(f"scripts/surface_scaled_bulk_mid_cover_{index:02d}_*_rerun.txt"))
    assert len(matches) == 1, (index, [p.name for p in matches])
    replay = matches[0]
    production = ROOT / "scripts" / replay.name.replace("_rerun.txt", ".txt")
    assert production.is_file() and replay.is_file()
    assert production.read_bytes() == replay.read_bytes()
    lines = production.read_text(encoding="utf-8").splitlines()
    beta = next(x.split() for x in lines if x.startswith("beta_domain "))
    rows = sum(x.startswith("trow ") for x in lines)
    validate(production, __import__("fractions").Fraction(beta[1]),
             __import__("fractions").Fraction(beta[2]))
    digest = sha(production)
    return {
        "name": production.stem.removeprefix("surface_scaled_bulk_"),
        "beta_domain": [beta[1], beta[2]],
        "t_rows": rows,
        "production": {"path": str(production.relative_to(ROOT)).replace("\\", "/"),
                        "sha256": digest},
        "replay": {"path": str(replay.relative_to(ROOT)).replace("\\", "/"),
                    "sha256": sha(replay)},
    }


def main() -> int:
    units = [make_unit(i) for i in range(48, 82)]
    assert units[0]["beta_domain"][0] == "241/4"
    assert units[-1]["beta_domain"][1] == "275/4"
    for left, right in zip(units, units[1:]):
        assert left["beta_domain"][1] == right["beta_domain"][0]
    manifest = {
        "schema_version": 1,
        "run_id": "surface-scaled-bulk-cwin3p2-mid24-terminal-20260725",
        "claim_scope": "CWIN=3/2 terminal direct-sign cover for beta [241/4,275/4]; no H_tail/G2/G6 promotion.",
        "status": "terminal_direct_sign_certified",
        "promotion": "NONE",
        "beta_union": ["241/4", "275/4"],
        "configuration": {"cwin": "3/2", "beta_order": 24,
                          "t_order": 25, "precision": 180,
                          "min_dt": "1/100000"},
        "units": units,
        "total_t_rows": sum(x["t_rows"] for x in units),
        "validator": {"path": "scripts/validate_surface_g2_mid24_terminal_manifest.py",
                       "verdict": "PENDING"},
    }
    OUT.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print("WROTE", OUT.relative_to(ROOT), "units", len(units),
          "rows", manifest["total_t_rows"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
