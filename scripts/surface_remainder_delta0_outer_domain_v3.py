"""Byte-separate outer-domain extension registered through delta=0.006."""

from contextlib import contextmanager
from fractions import Fraction
from functools import lru_cache

from flint import arb, arb_series

import surface_remainder_delta0_derivative_tail as endpoint
import surface_remainder_delta0_outer_domain_v2 as v2
from surface_bessel_integral_remainder import aq
from surface_remainder_delta0_series_design import PREC


MAX_DELTA = Fraction(3, 500)


def _require_delta(delta_max):
    if not isinstance(delta_max, Fraction):
        raise TypeError("delta_max must be an exact Fraction")
    if not Fraction(0) < delta_max <= MAX_DELTA:
        raise ValueError("v3 outer-domain contract ends at 3/500")
    return aq(delta_max)


@contextmanager
def _registered_domain():
    """Reuse v2 algebra under the v3 cap without changing v2 on disk."""
    original = v2._require_delta
    v2._require_delta = _require_delta
    try:
        yield
    finally:
        v2._require_delta = original


@lru_cache(maxsize=None)
def annulus_derivative_bounds(delta_max):
    _require_delta(delta_max)
    with _registered_domain():
        # Bypass v2's cache so no v3-domain value leaks into its endpoint.
        return v2.annulus_derivative_bounds.__wrapped__(delta_max)


@lru_cache(maxsize=None)
def outer_derivative_bounds(delta_max):
    annulus = annulus_derivative_bounds(delta_max)
    tail = endpoint.derivative_tail_bounds(32)
    return {name: [annulus[name][k]+tail[name][k]
                   for k in range(PREC)] for name in annulus}


def add_outer_derivatives(series, delta_max):
    outer = outer_derivative_bounds(delta_max)
    result = {}
    for name, value in series.items():
        coefficients = value.coeffs()+[arb(0)]*PREC
        result[name] = arb_series([
            coefficients[k]+outer[name][k]*arb("0 +/- 1")
            for k in range(PREC)
        ], PREC)
    return result


def direct_moving_band_value_coefficients(delta_max):
    _require_delta(delta_max)
    with _registered_domain():
        return v2.direct_moving_band_value_coefficients(delta_max)


def normalized_y_error_from_moment_coefficients(
        delta_max, kd_lower, moment_abs, error_coefficients):
    _require_delta(delta_max)
    with _registered_domain():
        return v2.normalized_y_error_from_moment_coefficients(
            delta_max, kd_lower, moment_abs, error_coefficients)

