"""Order-22 repair wrapper for exactly mid-cover units 09 and 29."""

import hashlib
from pathlib import Path

import run_surface_scaled_bulk_cwin3p2_mid_cover_order22_repair as base

base.PREREG = (
    "docs/SURFACE-G2-CWIN3P2-MID-COVER-ORDER22-REPAIR-UNITS09-29-PREREG-20260723.md"
)

ROOT = Path(__file__).resolve().parents[1]
_original_transcript = base.transcript


def transcript(index, lo, hi, rows, cache_entries):
    label, text = _original_transcript(index, lo, hi, rows, cache_entries)
    digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    marker = "dependency scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order22_repair.py"
    text = text.replace(
        marker,
        "dependency scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order22_repair_units09_29.py sha256 "
        + digest
        + "\n"
        + marker,
        1,
    )
    return label, text


base.transcript = transcript

if __name__ == "__main__":
    raise SystemExit(base.main())
