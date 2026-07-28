"""Isolated preregistered replacement lane for beta [765/16,193/4]."""
from __future__ import annotations

import re
from fractions import Fraction
from pathlib import Path

import run_surface_scaled_bulk_cwin3p2_mid_cover as base

ROOT = Path(__file__).resolve().parents[1]
base.START = Fraction(765, 16)
base.END = Fraction(193, 4)
base.WIDTH = base.END - base.START
base.ORDER = 20
base.T_ORDER = 25
base.PREC = 180
base.MIN_DT = Fraction(1, 100000)
base.CWIN = Fraction(3, 2)
base.PREREG = "docs/SURFACE-G2-CWIN3P2-MID-PREREG-20260722.md"
_transcript = base.transcript


def transcript(index, lo, hi, rows, cache_entries):
    label, text = _transcript(index, lo, hi, rows, cache_entries)
    text = text.replace(
        "scripts/run_surface_scaled_bulk_cwin3p2_mid_cover.py",
        "scripts/run_surface_scaled_bulk_cwin3p2_mid_gap_765_16_193_4.py",
    )
    path = ROOT / "scripts" / "run_surface_scaled_bulk_cwin3p2_mid_gap_765_16_193_4.py"
    digest = base.sha256(path)
    text = re.sub(
        r"(dependency scripts/run_surface_scaled_bulk_cwin3p2_mid_gap_765_16_193_4\.py sha256 )\S+",
        r"\g<1>" + digest,
        text,
    )
    return label, text


base.transcript = transcript


if __name__ == "__main__":
    raise SystemExit(base.main())
