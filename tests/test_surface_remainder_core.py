from __future__ import annotations

import sys
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))

import surface_remainder_core_l2_arb as core  # noqa: E402
from surface_remainder_centered_prefactor import Dual  # noqa: E402


def test_registered_cutoff_constants_and_junction_values() -> None:
    assert (core.R0, core.R1, core.DELTA_R2) == (4, 10, 84)
    assert core.cutoff_dual(Dual(arb(3)), Dual(arb(0))).v == 1
    assert core.cutoff_dual(Dual(arb(10)), Dual(arb(0))).v == 0


def test_transition_cutoff_and_hessians_are_finite() -> None:
    ctx.prec = 100
    value = core.cutoff_dual(
        Dual(core.hull(arb(5), arb(6)), arb(1)),
        Dual(core.hull(arb(1), arb(2)), arb(0), arb(1)),
    )
    assert all(component.is_finite() for component in (
        value.v, value.x, value.y, value.xx, value.xy, value.yy
    ))
    assert value.v.lower() >= 0
    assert value.v.upper() <= 1


def test_l1_cells_are_finite_in_both_charts() -> None:
    ctx.prec = 100
    for mirror in (False, True):
        values = core.localized_cell_bounds(
            arb(1)/15, arb("2.9"), arb(0), arb("0.625"),
            arb("8.125"), arb("8.75"), mirror=mirror,
        )
        assert all(value.is_finite() for value in values.values())
