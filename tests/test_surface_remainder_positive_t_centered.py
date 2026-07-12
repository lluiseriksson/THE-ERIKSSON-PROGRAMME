import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "positive_t_centered",
    ROOT/"scripts"/"surface_remainder_positive_t_centered.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_t_series_algebra_division_identity():
    a = [MOD.tjet(arb(2+i), arb(1-i)) for i in range(MOD.PREC)]
    product = MOD._smul(a, MOD._sinv(a))
    for index, value in enumerate(product):
        expected = arb(1) if index == 0 else arb(0)
        assert (value.v-expected).contains(0)
        assert value.d.contains(0)


def test_one_t_centered_cell_is_finite():
    ctx.prec = 100
    calibration = [arb(0) for _ in range(MOD.PREC)]
    values = MOD.centered_cell(
        arb("0.04975"), arb("2.9"), arb("2.9 +/- 0.001"),
        arb(0), arb("0.05"), arb(0), arb("0.05"), calibration)
    assert all(value.v.is_finite() and value.d.is_finite()
               for row in values.values() for value in row)


def test_t_derivative_encloses_symmetric_cell_difference():
    ctx.prec = 140
    h = arb("1e-6")
    t = arb("2.9")
    calibration = [arb(0) for _ in range(MOD.PREC)]
    values = MOD.centered_cell(
        arb("0.04975"), t, MOD.spatial.hull(t-h, t+h),
        arb(0), arb("0.02"), arb(0), arb("0.02"), calibration)
    plus = MOD.spatial.centered_cell(
        arb("0.04975"), t+h, arb(0), arb("0.02"),
        arb(0), arb("0.02"), calibration)
    minus = MOD.spatial.centered_cell(
        arb("0.04975"), t-h, arb(0), arb("0.02"),
        arb(0), arb("0.02"), calibration)
    for name in values:
        finite = (plus[name][0]-minus[name][0])/(2*h)
        assert (values[name][0].d-arb(finite.mid())).contains(0)
