"""Read-only aggregate audit of all archived scaled-bulk candidate lanes.

The child validators own the production/replay contracts.  This driver only
re-runs them and records the arithmetic coverage that is already archived; it
never edits a manifest and never promotes G2 or G6.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

# Ordered by beta, with the specialised CWIN=3/2 seam lanes after the regular
# candidate lanes.  The validators themselves check exact adjacency and replay
# identity for their own transcripts.
VALIDATORS = (
    "validate_surface_scaled_bulk_20_30_candidate.py",
    "validate_surface_scaled_bulk_30_31_candidate.py",
    "validate_surface_scaled_bulk_31_35_candidate.py",
    "validate_surface_scaled_bulk_35_36_candidate.py",
    "validate_surface_scaled_bulk_36_37_candidate.py",
    "validate_surface_scaled_bulk_37_40_candidate.py",
    "validate_surface_scaled_bulk_40_43_candidate.py",
    "validate_surface_scaled_bulk_43_45_candidate.py",
    "validate_surface_scaled_bulk_45_50_candidate.py",
    "validate_surface_scaled_bulk_50_51_candidate.py",
    "validate_surface_scaled_bulk_51_52_candidate.py",
    "validate_surface_scaled_bulk_52_60_candidate.py",
    "validate_surface_scaled_bulk_60_61_candidate.py",
    "validate_surface_scaled_bulk_61_63_candidate.py",
    "validate_surface_scaled_bulk_cwin3p2_mid_gap_765_16_193_4.py",
    "validate_surface_scaled_bulk_63_65_candidate.py",
    "validate_surface_scaled_bulk_65_66_candidate.py",
    "validate_surface_scaled_bulk_66_67_candidate.py",
    "validate_surface_scaled_bulk_67_67p25.py",
    "validate_surface_scaled_bulk_67_67p5.py",
    "validate_surface_scaled_bulk_67p5_68.py",
    "validate_surface_scaled_bulk_68_69.py",
    "validate_surface_scaled_bulk_cwin3p2_narrow_69_69p25.py",
    "validate_surface_scaled_bulk_cwin3p2_narrow_69_69p5.py",
    "validate_surface_scaled_bulk_cwin3p2_69p5_70.py",
    "validate_surface_scaled_bulk_cwin3p2_70_71.py",
    "validate_surface_scaled_bulk_cwin3p2_71_72.py",
    "validate_surface_scaled_bulk_cwin3p2_72_73.py",
    "validate_surface_scaled_bulk_cwin3p2_73_74.py",
    "validate_surface_scaled_bulk_cwin3p2_74_75.py",
    "validate_surface_scaled_bulk_cwin3p2_75_76.py",
    "validate_surface_scaled_bulk_cwin3p2_76_77.py",
    "validate_surface_scaled_bulk_cwin3p2_77_78_mixed.py",
    "validate_surface_scaled_bulk_cwin3p2_high_78p25_78p875.py",
    "validate_surface_scaled_bulk_cwin3p2_high_100.py",
    "validate_surface_scaled_bulk_cwin3p2_high_100p0625.py",
    # This aggregate validator owns the 56-unit order-40/order-45 high
    # archive, including the units whose names are generated from rescue
    # intervals rather than having one child validator each.
    "audit_surface_scaled_bulk_cwin3p2_high_union.py",
)


def _rows(text: str) -> int | None:
    match = re.search(r"(?:t_rows|rows)\s+(\d+)", text)
    return int(match.group(1)) if match else None


def main() -> int:
    total_rows = 0
    passed = 0
    for name in VALIDATORS:
        path = ROOT / "scripts" / name
        if not path.is_file():
            print(f"MISSING {name}", flush=True)
            return 2
        result = subprocess.run(
            [sys.executable, str(path)], cwd=ROOT, text=True,
            capture_output=True, check=False,
        )
        output = (result.stdout + result.stderr).strip()
        print(f"[{name}] exit={result.returncode}", flush=True)
        if output:
            print(output, flush=True)
        if result.returncode:
            return result.returncode or 1
        rows = _rows(output)
        if rows is not None:
            total_rows += rows
        passed += 1
    print(
        f"FULL SCALED-BULK CANDIDATE AUDIT PASS validators={passed}/{len(VALIDATORS)} "
        f"reported_t_rows={total_rows}", flush=True,
    )
    print("CANDIDATE ONLY; NO G2/G6 PROMOTION", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
