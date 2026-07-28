import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_series_design",
    ROOT/"scripts"/"surface_remainder_delta0_series_design.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_sinc_delta_series_contains_independent_values():
    ctx.prec = 140
    scale = arb("2.25")
    series = MOD.sinc2_affine_delta(arb(0), scale)
    for value in (arb(0), arb("0.001"), arb("0.01")):
        polynomial = sum((coefficient*value**k
                          for k, coefficient in enumerate(series.coeffs())),
                         arb(0))
        exact = (scale*value).sqrt().sin()**2/(scale*value) \
            if value != 0 else arb(1)
        # This checks the retained coefficients numerically; the design
        # driver does not claim its omitted delta tail is enclosed here.
        assert abs(float(polynomial.mid()-exact.mid())) < 1e-8


def test_nominal_series_is_finite_at_delta_zero():
    ctx.prec = 140
    values = MOD.nominal_moment_series(
        arb(0), arb("2.9"), arb("3 +/- 0.01"), arb("2 +/- 0.01"))
    assert all(coefficient.is_finite()
               for series in values.values() for coefficient in series.coeffs())


def test_b_over_delta_derivative_identity_stays_finite():
    ctx.prec = 140
    lane = MOD.hull(arb(0), arb("0.001"))
    values = MOD.normalized_y_derivative_enclosure(
        lane, arb("2.9"), grid=48)
    assert len(values.coeffs()) == MOD.PREC-2
    assert all(value.is_finite() for value in values.coeffs())
