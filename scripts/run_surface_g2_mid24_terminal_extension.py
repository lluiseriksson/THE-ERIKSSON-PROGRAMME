"""Fresh terminal-contract runner for the lower order-24 beta extension."""

from __future__ import annotations

import hashlib
from pathlib import Path

import run_surface_scaled_bulk_cwin3p2_mid_cover_order24_repair_extension5 as base

ROOT = Path(__file__).resolve().parents[1]
PREREG = "docs/SURFACE-G2-MID24-TERMINAL-EXTENSION-PREREG-20260725.md"
base.base.PREREG = PREREG
_base_transcript = base.transcript


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def transcript(index, lo, hi, rows, cache_entries):
    label, text = _base_transcript(index, lo, hi, rows, cache_entries)
    text = text.replace(
        "SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER24 REPAIR EXTENSION5",
        "SCALED BULK SIGN ROW MID TERMINAL ORDER24",
        1,
    )
    text = text.replace(
        "SCOPE quarantined order24 repair extension5; no G2/G6 promotion",
        "SCOPE terminal direct-sign mid24 gap; no H_tail promotion",
        1,
    )
    wrapper = "scripts/run_surface_g2_mid24_terminal_extension.py"
    text = text.replace(
        "SCALED BULK SIGN ROW MID TERMINAL ORDER24\n",
        f"dependency {wrapper} sha256 {sha(ROOT / wrapper)}\n"
        "SCALED BULK SIGN ROW MID TERMINAL ORDER24\n",
        1,
    )
    text = text.replace(
        "dependency docs/SURFACE-G2-MID24-TERMINAL-PREREG-20260725.md sha256 ",
        "dependency docs/SURFACE-G2-MID24-TERMINAL-EXTENSION-PREREG-20260725.md sha256 ",
        1,
    )
    return label, text


base.transcript = transcript
base.base.transcript = transcript


if __name__ == "__main__":
    raise SystemExit(base.base.main())
