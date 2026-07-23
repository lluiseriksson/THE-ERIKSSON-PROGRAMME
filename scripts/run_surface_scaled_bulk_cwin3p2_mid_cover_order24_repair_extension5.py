"""Order-24 extension 5 for the finite-beta sign-cover design lane.

This wrapper is byte-separate from earlier repairs and never changes the
authoritative Bessel backend on disk.  Its outputs are candidate-only.
"""
from __future__ import annotations

import re
from pathlib import Path

import run_surface_scaled_bulk_cwin3p2_mid_cover_order22_repair as base

ROOT = Path(__file__).resolve().parents[1]
base.ORDER = 24
base.PREREG = "docs/SURFACE-G2-CWIN3P2-MID-COVER-ORDER24-REPAIR-EXTENSION5-PREREG-20260723.md"
_transcript = base.transcript


def transcript(index, lo, hi, rows, cache_entries):
    label, text = _transcript(index, lo, hi, rows, cache_entries)
    text = text.replace("ORDER22 REPAIR", "ORDER24 REPAIR EXTENSION5")
    text = text.replace("order22 repair", "order24 repair extension5")
    text = text.replace(
        "scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order22_repair.py",
        "scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order24_repair_extension5.py",
    )
    path = ROOT / "scripts" / "run_surface_scaled_bulk_cwin3p2_mid_cover_order24_repair_extension5.py"
    digest = base.sha256(path)
    text = re.sub(
        r"(dependency scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order24_repair_extension5\.py sha256 )\S+",
        r"\g<1>" + digest,
        text,
    )
    return label, text


base.transcript = transcript

if __name__ == "__main__":
    raise SystemExit(base.main())
