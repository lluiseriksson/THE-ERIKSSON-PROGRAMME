"""Validate a frontier high-order pair emitted by the generic wrapper."""

from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path

from validate_surface_scaled_bulk_cwin3p2_high_unit import parse


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    unit = args.unit
    lo, hi = Fraction(args.lo), Fraction(args.hi)
    production = ROOT / "scripts" / f"surface_scaled_bulk_{unit}.txt"
    replay = ROOT / "scripts" / f"surface_scaled_bulk_{unit}_rerun.txt"
    first, count = parse(production, unit, lo, hi)
    second, count2 = parse(replay, unit, lo, hi)
    assert first == second
    assert count == count2
    print("FRONTIER CWIN3P2 HIGH VALIDATION PASS", unit, "t_rows", count)


if __name__ == "__main__":
    main()
