"""Fresh terminal-contract runner for the final beta gap, slice 1."""

from __future__ import annotations

import hashlib
import subprocess
import sys
from pathlib import Path

from flint import ctx

import run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30 as base

ROOT = Path(__file__).resolve().parents[1]
_base_make_text = base.make_text


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def make_text(rows, replay: bool) -> str:
    text = _base_make_text(rows, replay)
    wrapper = "scripts/run_surface_g2_unit82_terminal.py"
    digest = sha(ROOT / wrapper)
    text = text.replace(
        "SCALED BULK SIGN ROW UNIT82 RESCUE ORDER30",
        "SCALED BULK SIGN ROW UNIT82 TERMINAL ORDER30",
        1,
    )
    text = text.replace(
        "SCOPE quarantined unit82 rescue; no G2/G6 promotion",
        "SCOPE terminal direct-sign unit82 slice1; no H_tail promotion",
        1,
    )
    text = text.replace(
        "SCALED BULK SIGN ROW PASS\n",
        f"dependency {wrapper} sha256 {digest}\nSCALED BULK SIGN ROW PASS\n",
        1,
    )
    return text


base.make_text = make_text


if __name__ == "__main__":
    raise SystemExit(base.main() or 0)
