"""Validate the frozen design-checkpoint union for the delta<=0.009 route.

This is deliberately a design validator, not a production certificate.  It
accepts the frozen parent rows 0,...,154 and 157, plus the pre-registered
dyadic replacement of parents 155 and 156.  It never treats a failed parent
or a coarse failed child as part of the cover.
"""

import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from flint import arb

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_009_checkpoint as checkpoint
import surface_remainder_delta0_r4_extension_009_tail_bisection as tail


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
PARENT_INDICES = tuple(range(155)) + (157,)
TAIL_UNITS = (
    (155, 1, 0),
    (155, 1, 1),
    (156, 1, 0),
    (156, 2, 2),
    (156, 2, 3),
)
RADIUS = Fraction(62, 5)


@dataclass(frozen=True)
class Unit:
    path: Path
    lo: Fraction
    hi: Fraction
    grid: int
    terminal: str
    label: str


def expected_units():
    boxes = list(regular.sealed.born_t_boxes())
    units = []
    for index in PARENT_INDICES:
        lo, hi = boxes[index]
        units.append(Unit(
            SCRIPTS / (
                "surface_remainder_delta0_r4_extension_009_checkpoint_"
                f"{index:03d}_design.txt"
            ),
            lo,
            hi,
            checkpoint.fixed.grid_for(index),
            f"R4 009 BAND-GAP CHECKPOINT DESIGN PASS {index} "
            "FULL UNION AND PRODUCTION REQUIRED",
            f"parent {index}",
        ))
    for index, depth, part in TAIL_UNITS:
        lo, hi = tail.subbox(index, depth, part)
        units.append(Unit(
            SCRIPTS / (
                "surface_remainder_delta0_r4_extension_009_tail_"
                f"{index}_d{depth}_p{part}_design.txt"
            ),
            lo,
            hi,
            tail.GRID,
            f"R4 009 BAND-GAP TAIL BISECTION DESIGN PASS {index} "
            f"{depth} {part} FULL UNION AND PRODUCTION REQUIRED",
            f"tail {index}/{depth}/{part}",
        ))
    return tuple(sorted(units, key=lambda unit: (unit.lo, unit.hi)))


def parse_row(unit):
    lines = unit.path.read_text(encoding="utf-8").splitlines()
    if lines.count(unit.terminal) != 1 or lines[-1] != unit.terminal:
        raise AssertionError(f"missing terminal PASS: {unit.label}")
    if any(" FAIL" in line for line in lines):
        raise AssertionError(f"failure marker: {unit.label}")
    rows = [line for line in lines if line.startswith("ROW ")]
    if len(rows) != 1:
        raise AssertionError(f"row count: {unit.label}")
    match = re.search(
        r" t (\S+) (\S+) grid (\d+) radius (\S+) .* "
        r"margin_lower (.+)$",
        rows[0],
    )
    if match is None:
        raise AssertionError(f"row syntax: {unit.label}")
    lo, hi = Fraction(match.group(1)), Fraction(match.group(2))
    grid, radius = int(match.group(3)), Fraction(match.group(4))
    margin = arb(match.group(5))
    if (lo, hi, grid, radius) != (unit.lo, unit.hi, unit.grid, RADIUS):
        raise AssertionError(f"row contract: {unit.label}")
    if not margin > 0:
        raise AssertionError(f"nonpositive margin: {unit.label}")
    return margin


def validate():
    units = expected_units()
    endpoint = list(regular.sealed.born_t_boxes())[-1][1]
    if len(units) != 161:
        raise AssertionError("frozen unit count")
    if units[0].lo != 0 or units[-1].hi != endpoint:
        raise AssertionError("cover endpoints")
    if any(left.hi != right.lo for left, right in zip(units, units[1:])):
        raise AssertionError("gap or overlap in frozen union")
    margins = [(parse_row(unit), unit) for unit in units]
    margin, unit = min(margins, key=lambda item: float(item[0]))
    print(
        "K2 delta 0.009 DESIGN checkpoints OK: 161 units, "
        "band radius 62/5, worst",
        unit.label,
        "margin_lower",
        margin,
        "PRODUCTION STILL REQUIRED",
    )


if __name__ == "__main__":
    validate()
