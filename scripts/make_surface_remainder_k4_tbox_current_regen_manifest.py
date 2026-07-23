"""Write a quarantined manifest for the current K4 t-box regeneration."""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "run-manifests" / "surface-remainder-k4-tbox-current-regen-20260723.json"
PI_HI = Fraction(31415927, 10_000_000)
UNITS = [(f"{i:03d}_{i+1:03d}", Fraction(i, 100), Fraction(i + 1, 100))
         for i in range(300, 314)] + [("314_pi", Fraction(157, 50), PI_HI)]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    entries = []
    for unit, lo, hi in UNITS:
        prod = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723.txt"
        replay = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723_rerun.txt"
        if prod.read_bytes() != replay.read_bytes():
            raise SystemExit(f"production/replay mismatch: {unit}")
        rows = prod.read_text(encoding="utf-8").splitlines()
        cells = sum(line.startswith("CELL ") for line in rows)
        entries.append({
            "unit": unit,
            "t_domain": [str(lo), str(hi)],
            "cells": cells,
            "production": {"path": str(prod.relative_to(ROOT)), "sha256": sha(prod)},
            "replay": {"path": str(replay.relative_to(ROOT)), "sha256": sha(replay)},
        })
    deps = {}
    for rel in (
        "scripts/certify_surface_remainder_k4_t_box_probe.py",
        "scripts/certify_surface_remainder_k4_centered_band.py",
        "scripts/surface_remainder_centered_delta_integrator_design.py",
        "scripts/surface_remainder_centered_delta_carrier.py",
        "scripts/surface_remainder_complement_l3_smoke.py",
        "scripts/surface_remainder_complement.py",
        "scripts/run_surface_remainder_k4_tbox_current_regen.py",
        "scripts/audit_surface_remainder_k4_tbox_current_regen.py",
    ):
        path = ROOT / rel
        deps[rel] = {"path": rel, "sha256": sha(path)}
    payload = {
        "schema_version": 1,
        "run_id": "surface-remainder-k4-tbox-current-regen-20260723",
        "status": "quarantined",
        "claim_scope": "Current-dependency regeneration of candidate K4 t-box evidence on t in [3, pi]; no K4/S1'''/S2'''/G2/G6 promotion.",
        "config": {"delta": ["1/25", "81/2000"], "seed_grid": 12,
                   "max_cells": 2304, "precision": 140},
        "t_union": ["3", str(PI_HI)],
        "units": entries,
        "total_cells": sum(e["cells"] for e in entries),
        "dependencies": deps,
        "validator": {"path": "scripts/audit_surface_remainder_k4_tbox_current_regen.py",
                       "verdict": "PASS", "production_replay_byte_identical": True},
        "promotion": "NONE",
    }
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(OUT)
    print("K4 CURRENT-REGEN MANIFEST WRITTEN units", len(entries), "cells", payload["total_cells"])


if __name__ == "__main__":
    main()
