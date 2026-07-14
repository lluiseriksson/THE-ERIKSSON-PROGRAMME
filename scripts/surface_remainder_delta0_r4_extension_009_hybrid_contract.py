"""Frozen hybrid regular/right-edge partition for the ninth delta birth.

The already certified rectangle delta<=1/125 keeps its full-t coverage.
Only the new birth [1/125,9/1000] is split: exact-r4 covers t<=3.13,
and t>=3.13 is assigned to the moving-right-edge obligation.  This module
contains geometry and unit selection only; it makes no numerical claim.
"""

from dataclasses import dataclass
from fractions import Fraction

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_009_checkpoint as checkpoint
import surface_remainder_delta0_r4_extension_009_tail_bisection as tail


OLD_DELTA_MAX = Fraction(1, 125)
NEW_DELTA_MAX = Fraction(9, 1000)
CWIN = Fraction(3, 2)
T_CUT = Fraction(313, 100)
PARENT_INDICES = tuple(range(155))
TAIL_UNITS = ((155, 1, 0), (155, 1, 1), (156, 1, 0))


@dataclass(frozen=True)
class Unit:
    kind: str
    index: int
    depth: int
    part: int
    lo: Fraction
    hi: Fraction
    grid: int

    @property
    def slug(self):
        if self.kind == "parent":
            return f"parent_{self.index:03d}"
        return f"tail_{self.index}_d{self.depth}_p{self.part}"


def pi_hi():
    return list(regular.sealed.born_t_boxes())[-1][1]


def edge_starts_no_later_than_cut():
    """Exact inclusion [T_CUT,pi] in d<=3*delta/2 for the new birth."""
    return pi_hi() - CWIN * OLD_DELTA_MAX <= T_CUT


def regular_units():
    boxes = list(regular.sealed.born_t_boxes())
    units = []
    for index in PARENT_INDICES:
        lo, hi = boxes[index]
        units.append(Unit(
            "parent", index, 0, 0, lo, hi,
            checkpoint.fixed.grid_for(index),
        ))
    for index, depth, part in TAIL_UNITS:
        lo, hi = tail.subbox(index, depth, part)
        units.append(Unit("tail", index, depth, part, lo, hi, tail.GRID))
    return tuple(sorted(units, key=lambda unit: (unit.lo, unit.hi)))


def assert_contract():
    units = regular_units()
    assert OLD_DELTA_MAX < NEW_DELTA_MAX
    assert edge_starts_no_later_than_cut()
    assert len(units) == 158
    assert units[0].lo == 0 and units[-1].hi == T_CUT
    assert all(left.hi == right.lo for left, right in zip(units, units[1:]))


assert_contract()
