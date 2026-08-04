import importlib.util
from pathlib import Path
import sys

from flint import ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_derivative_tail",
    ROOT/"scripts"/"surface_remainder_delta0_derivative_tail.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_polynomial_gaussian_tail_is_finite():
    ctx.prec = 160
    tails = MOD.derivative_tail_bounds()
    assert set(tails) == {"kd", "kf", "hdd", "hdf"}
    assert all(len(row) == MOD.ORDER+1 for row in tails.values())
    assert all(value.is_finite() and value > 0
               for row in tails.values() for value in row)


def test_tail_contracts_when_radius_increases():
    ctx.prec = 160
    term = MOD.Term(MOD.arb(10), 40)
    assert MOD.radial_tail(term, 31) < MOD.radial_tail(term, 30)


def test_moving_band_is_fifth_order_flat():
    ctx.prec = 160
    bands = MOD.moving_band_value_coefficients()
    assert all(value.is_finite() and value > 0 for value in bands.values())
    assert max(value.upper() for value in bands.values()) < 5
