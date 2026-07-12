import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "positive_physical_series",
    ROOT/"scripts"/"surface_remainder_positive_physical_series_design.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_physical_series_stays_finite_on_positive_box():
    ctx.prec = 140
    values = MOD.physical_moment_series(
        MOD.hull(arb("0.049"), arb("0.05")), arb("2.9"),
        MOD.Dual(arb("0.4 +/- 0.01"), arb(1)),
        MOD.Dual(arb("0.3 +/- 0.01"), arb(0), arb(1)))
    assert all(component.v.is_finite()
               for series in values.values() for component in series)


def test_centered_cell_integrals_are_finite():
    ctx.prec = 140
    values = MOD.centered_cell(
        MOD.hull(arb("0.049"), arb("0.05")), arb("2.9"),
        arb(0), arb("0.05"), arb(0), arb("0.05"))
    assert all(value.is_finite()
               for coefficients in values.values() for value in coefficients)


def test_terminal_weights_are_nonnegative():
    ctx.prec = 100
    delta = MOD.hull(arb("0.049"), arb("0.05"))
    pilot = MOD.integrate_moments(delta, arb("2.9"), 12)
    weights = MOD.terminal_weights(pilot, delta)
    assert len(weights) == 4*MOD.PREC
    assert all(value >= 0 for value in weights.values())
