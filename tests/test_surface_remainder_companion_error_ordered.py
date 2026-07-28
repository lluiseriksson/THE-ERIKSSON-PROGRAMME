import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx
import pytest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "companion_error_ordered",
    ROOT/"scripts"/"surface_remainder_companion_error_ordered.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_order_six_actual_charge_improves_order_four():
    ctx.prec = 150
    delta = arb("0.05")
    order4 = MOD.normalized_y_error_coefficient(
        delta, arb(2), arb(10), order=4)*delta**4
    order6 = MOD.normalized_y_error_coefficient(
        delta, arb(2), arb(10), order=6)*delta**6
    assert order6 < order4
    with pytest.raises(ValueError, match="negative"):
        MOD.moment_error_coefficients(-1)
