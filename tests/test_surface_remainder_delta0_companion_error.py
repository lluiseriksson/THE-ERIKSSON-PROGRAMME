import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx
import pytest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_companion_error",
    ROOT/"scripts"/"surface_remainder_delta0_companion_error.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_moment_errors_are_fifth_order_and_finite():
    ctx.prec = 150
    errors = MOD.moment_error_coefficients()
    assert all(value.is_finite() and value > 0
               for value in errors.__dict__.values())
    assert errors.kd < 1 and errors.hdf < 4


def test_quotient_charge_is_two_orders_below_endpoint_budget():
    ctx.prec = 150
    coefficient = MOD.normalized_y_error_coefficient(
        arb("0.001"), arb(2), arb(10))
    # Divide C*delta^4 by the direct judge's delta^2 scale.
    assert coefficient*arb("0.001")**2 < arb("0.001")


def test_higher_companion_order_has_smaller_actual_lane_charge():
    ctx.prec = 150
    delta = arb("0.05")
    order4 = MOD.normalized_y_error_coefficient(
        delta, arb(2), arb(10), order=4)*delta**4
    order6 = MOD.normalized_y_error_coefficient(
        delta, arb(2), arb(10), order=6)*delta**6
    assert order6 < order4
    default = MOD.moment_error_coefficients()
    explicit = MOD.moment_error_coefficients(order=4)
    assert all((getattr(default, name)-getattr(explicit, name)).contains(0)
               for name in default.__dict__)
    with pytest.raises(ValueError, match="negative"):
        MOD.moment_error_coefficients(order=-1)
