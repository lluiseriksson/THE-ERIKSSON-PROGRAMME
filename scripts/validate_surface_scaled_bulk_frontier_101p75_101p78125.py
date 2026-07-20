"""Validate the frontier high-order pair using the wrapper's exact filenames."""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from validate_surface_scaled_bulk_cwin3p2_high_unit import parse


ROOT = Path(__file__).resolve().parents[1]
UNIT = "101p75_101p78125"
LO = Fraction(407, 4)
HI = Fraction(3257, 32)


def main() -> None:
    production = ROOT / "scripts" / f"surface_scaled_bulk_{UNIT}.txt"
    replay = ROOT / "scripts" / f"surface_scaled_bulk_{UNIT}_rerun.txt"
    first, count = parse(production, UNIT, LO, HI)
    second, count2 = parse(replay, UNIT, LO, HI)
    assert first == second
    assert count == count2
    print("FRONTIER CWIN3P2 HIGH VALIDATION PASS", UNIT, "t_rows", count)


if __name__ == "__main__":
    main()
