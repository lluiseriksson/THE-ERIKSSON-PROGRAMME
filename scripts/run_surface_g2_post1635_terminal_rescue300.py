"""Terminal-contract wrapper for one post-1635 rescue-300 box."""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from pathlib import Path

import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_rescue300 as base

ROOT = Path(__file__).resolve().parents[1]
PREREG = ROOT / "docs" / "SURFACE-G2-POST1635-RESCUE300-TERMINAL-PREREG-20260725.md"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def render(unit: str, lo: Fraction, hi: Fraction) -> str:
    text = base.run(unit, lo, hi)
    lines = text.splitlines()
    lines[0] = "SCALED BULK SIGN ROW POST1635 TERMINAL RESCUE300"
    insert = next(i for i, line in enumerate(lines) if line.startswith("trow "))
    lines.insert(insert, f"dependency scripts/run_surface_g2_post1635_terminal_rescue300.py sha256 {sha(ROOT / 'scripts/run_surface_g2_post1635_terminal_rescue300.py')}")
    lines.insert(insert + 1, f"dependency docs/SURFACE-G2-POST1635-RESCUE300-TERMINAL-PREREG-20260725.md sha256 {sha(PREREG)}")
    for i, line in enumerate(lines):
        if line.startswith("SCOPE "):
            lines[i] = "SCOPE terminal direct-sign post1635 gap; no H_tail promotion"
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    print(render(args.unit, Fraction(args.lo), Fraction(args.hi)), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
