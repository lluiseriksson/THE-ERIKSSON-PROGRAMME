"""Frozen geometry for the tenth K2 regular birth [0.009,0.01]."""

from dataclasses import dataclass
from fractions import Fraction

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_009_checkpoint as checkpoint
import surface_remainder_delta0_r4_extension_009_tail_bisection as tail


OLD_DELTA_MAX = Fraction(9, 1000)
NEW_DELTA_MAX = Fraction(1, 100)
CWIN = Fraction(3, 2)
T_CUT = Fraction(313, 100)

CORE_BOXES = (
    (Fraction(0), Fraction(1, 200)),
    (Fraction(1, 200), Fraction(3, 500)),
    (Fraction(3, 500), Fraction(7, 1000)),
    (Fraction(7, 1000), Fraction(1, 125)),
    (Fraction(1, 125), Fraction(9, 1000)),
    (Fraction(9, 1000), Fraction(1, 100)),
)
ANNULUS_BOXES = tuple(
    (Fraction(j, 1000), Fraction(j+1, 1000)) for j in range(10)
)
PARENT_INDICES = tuple(range(155))
TAIL_UNITS = ((155, 1, 0), (155, 1, 1), (156, 1, 0))
WITNESSES = ((0, 384), (50, 192), (156, 384))


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
    return pi_hi() - CWIN * OLD_DELTA_MAX <= T_CUT


def regular_units():
    boxes = list(regular.sealed.born_t_boxes())
    units = [Unit("parent", i, 0, 0, boxes[i][0], boxes[i][1],
                  checkpoint.fixed.grid_for(i)) for i in PARENT_INDICES]
    units.extend(
        Unit("tail", i, depth, part, tail.subbox(i, depth, part)[0],
             tail.subbox(i, depth, part)[1], tail.GRID)
        for i, depth, part in TAIL_UNITS
    )
    return tuple(sorted(units, key=lambda unit: (unit.lo, unit.hi)))


def assert_contract():
    units = regular_units()
    assert OLD_DELTA_MAX < NEW_DELTA_MAX
    assert edge_starts_no_later_than_cut()
    assert len(units) == 158
    assert units[0].lo == 0 and units[-1].hi == T_CUT
    assert all(left.hi == right.lo for left, right in zip(units, units[1:]))
    assert ANNULUS_BOXES[-1][1] == NEW_DELTA_MAX


assert_contract()
