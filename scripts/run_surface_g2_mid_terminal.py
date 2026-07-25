"""Fresh terminal-contract runner for the first finite-beta gap."""

from __future__ import annotations

import hashlib
from pathlib import Path

import run_surface_scaled_bulk_cwin3p2_mid_cover_order22_repair as base

ROOT = Path(__file__).resolve().parents[1]
_base_transcript = base.transcript


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def transcript(index, lo, hi, rows, cache_entries):
    label, text = _base_transcript(index, lo, hi, rows, cache_entries)
    text = text.replace(
        "SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER22 REPAIR",
        "SCALED BULK SIGN ROW MID TERMINAL ORDER22",
        1,
    )
    text = text.replace(
        "SCOPE quarantined order22 repair; no G2/G6 promotion",
        "SCOPE terminal direct-sign mid gap; no H_tail promotion",
        1,
    )
    prereg = "docs/SURFACE-G2-MID-TERMINAL-PREREG-20260725.md"
    old_prereg = "docs/SURFACE-G2-CWIN3P2-MID-COVER-ORDER22-REPAIR-PREREG-20260722.md"
    text = text.replace(old_prereg, prereg, 1)
    text = text.replace(
        _base_transcript(index, lo, hi, rows, cache_entries)
        .split(f"dependency {old_prereg} sha256 ", 1)[1].split("\n", 1)[0],
        sha(ROOT / prereg),
        1,
    )
    wrapper = "scripts/run_surface_g2_mid_terminal.py"
    text = text.replace(
        "SCALED BULK SIGN ROW PASS\n",
        f"dependency {wrapper} sha256 {sha(ROOT / wrapper)}\nSCALED BULK SIGN ROW PASS\n",
        1,
    )
    return label, text


base.transcript = transcript


if __name__ == "__main__":
    raise SystemExit(base.main())
