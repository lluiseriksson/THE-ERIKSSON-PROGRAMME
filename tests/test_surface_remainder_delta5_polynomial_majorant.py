import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta5_poly", ROOT/"scripts"/"surface_remainder_delta5_polynomial_majorant.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_polynomial_bound_multiplication_preserves_degrees():
    value = MOD.pmul({2: arb(3), 4: arb(5)}, {0: arb(7), 2: arb(11)})
    assert value == {2: arb(21), 4: arb(68), 6: arb(55)}


def test_sixth_moment_bounds_are_finite():
    ctx.prec = 140
    bounds = MOD.sixth_moment_bounds()
    assert all(value.is_finite() and value > 0 for value in bounds.values())
