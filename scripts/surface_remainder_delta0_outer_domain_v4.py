"""Byte-separate outer-domain extension registered through delta=0.007."""

from contextlib import contextmanager
from fractions import Fraction
from functools import lru_cache

import surface_remainder_delta0_outer_domain_v3 as v3
from surface_bessel_integral_remainder import aq


MAX_DELTA = Fraction(7, 1000)


def _require_delta(delta_max):
    if not isinstance(delta_max, Fraction):
        raise TypeError("delta_max must be an exact Fraction")
    if not Fraction(0) < delta_max <= MAX_DELTA:
        raise ValueError("v4 outer-domain contract ends at 7/1000")
    return aq(delta_max)


@contextmanager
def _registered_domain():
    original = v3._require_delta
    v3._require_delta = _require_delta
    try:
        yield
    finally:
        v3._require_delta = original


@lru_cache(maxsize=None)
def outer_derivative_bounds_box_to(delta_lo, delta_hi, physical_inner):
    _require_delta(delta_hi)
    with _registered_domain():
        return v3.outer_derivative_bounds_box_to.__wrapped__(
            delta_lo, delta_hi, physical_inner)


def add_outer_derivatives_box_to(series, delta_lo, delta_hi,
                                 physical_inner):
    outer = outer_derivative_bounds_box_to(
        delta_lo, delta_hi, physical_inner)
    result = {}
    for name, value in series.items():
        coefficients = value.coeffs()+[v3.arb(0)]*v3.PREC
        result[name] = v3.arb_series([
            coefficients[k]+outer[name][k]*v3.arb("0 +/- 1")
            for k in range(v3.PREC)], v3.PREC)
    return result


def direct_moving_band_value_coefficients_from(delta_max, physical_inner):
    _require_delta(delta_max)
    with _registered_domain():
        return v3.direct_moving_band_value_coefficients_from(
            delta_max, physical_inner)


def normalized_y_error_from_moment_coefficients(
        delta_max, kd_lower, moment_abs, errors):
    _require_delta(delta_max)
    with _registered_domain():
        return v3.normalized_y_error_from_moment_coefficients(
            delta_max, kd_lower, moment_abs, errors)

