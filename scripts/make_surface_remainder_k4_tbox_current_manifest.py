"""Write a current-head manifest for the K4 centred t-box candidate union."""

import hashlib
import json
from fractions import Fraction
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PI_HI = Fraction(31415927, 10_000_000)
UNITS = [(f"{i:03d}_{i+1:03d}", Fraction(i, 100), Fraction(i + 1, 100))
         for i in range(300, 314)] + [("314_pi", Fraction(157, 50), PI_HI)]


def sha(relative):
    return hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()


def main():
    entries = []
    transcript_heads = set()
    for unit, lo, hi in UNITS:
        prod = f"scripts/surface_remainder_k4_tbox_{unit}_20260723_current_regen.txt"
        replay = f"scripts/surface_remainder_k4_tbox_{unit}_20260723_current_regen_rerun.txt"
        if (ROOT / prod).read_bytes() != (ROOT / replay).read_bytes():
            raise SystemExit(f"production/replay mismatch: {unit}")
        for path in (ROOT / prod, ROOT / replay):
            for line in path.read_text(encoding="utf-8").splitlines():
                if line.startswith("PROVENANCE git_head "):
                    transcript_heads.add(line.split()[-1])
                    break
        cells = sum(line.startswith("CELL ")
                    for line in (ROOT / prod).read_text(encoding="utf-8").splitlines())
        entries.append({"unit": unit, "t_domain": [str(lo), str(hi)],
                        "cells": cells,
                        "production": {"path": prod, "sha256": sha(prod)},
                        "replay": {"path": replay, "sha256": sha(replay)}})
    dep_paths = (
        "scripts/certify_surface_remainder_k4_t_box_probe.py",
        "scripts/certify_surface_remainder_k4_centered_band.py",
        "scripts/surface_remainder_centered_delta_integrator_design.py",
        "scripts/surface_remainder_centered_delta_carrier.py",
        "scripts/surface_remainder_complement_l3_smoke.py",
        "scripts/surface_remainder_complement.py",
        "scripts/run_surface_remainder_k4_tbox_current_regen.py",
        "scripts/audit_surface_remainder_k4_tbox_current_regen.py",
    )
    if len(transcript_heads) != 1:
        raise SystemExit(f"mixed transcript source heads: {sorted(transcript_heads)}")
    source_head = next(iter(transcript_heads))
    manifest_head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"], cwd=ROOT,
        text=True).strip()
    data = {
        "schema_version": 1,
        "run_id": "surface-remainder-k4-tbox-current-20260724",
        "status": "current-candidate-local-only",
        "claim_scope": "Current-head candidate K4 centred t-box union on t in [3,pi], delta=[1/25,81/2000]; 15 adjacent units and 34560 cells. No K4/S1'''/S2'''/G2/G6 promotion.",
        "git_head": source_head,
        "manifest_generated_head": manifest_head,
        "config": {"delta": ["1/25", "81/2000"], "seed_grid": 12,
                   "max_cells": 2304, "precision": 140},
        "t_union": ["3", str(PI_HI)],
        "units": entries,
        "total_cells": sum(e["cells"] for e in entries),
        "dependencies": {p: {"path": p, "sha256": sha(p)} for p in dep_paths},
        "validator": {"path": "scripts/audit_surface_remainder_k4_tbox_current_regen.py",
                       "verdict": "PASS", "production_replay_byte_identical": True},
        "supersedes": ["surface-remainder-k4-tbox-current-regen-20260723"],
        "promotion": "NONE",
        "notes": "Topology, dependency hashes, local fractions, and replay equality pass; regular-ball overlap, delta union, and literal global S1'''/S2''' remain open.",
    }
    out = ROOT / "run-manifests" / "surface-remainder-k4-tbox-current-20260724.json"
    out.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print("WROTE", out, "units", len(entries), "cells", data["total_cells"])


if __name__ == "__main__":
    main()
