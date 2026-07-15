"""Byte-separate outer-domain wrapper for the tenth K2 birth.

The v6 implementation is algebraically unchanged; this module only widens
its explicitly checked delta cap from ``9/1000`` to ``1/100`` while patching
the v6 local domain guard for the duration of each call.  Keeping the wrapper
separate prevents a tenth-birth experiment from changing any v6 transcript
or cache entry.  It carries no certificate by itself.
"""

from contextlib import contextmanager
from fractions import Fraction

import surface_remainder_delta0_outer_domain_v6 as v6


MAX_DELTA = Fraction(1, 100)


def _require_delta(delta_max):
    if not isinstance(delta_max, Fraction):
        raise TypeError("delta_max must be an exact Fraction")
    if not Fraction(0) < delta_max <= MAX_DELTA:
        raise ValueError("v7 outer-domain contract ends at 1/100")
    return v6.aq(delta_max)


@contextmanager
def _widened_domain():
    old_max = v6.MAX_DELTA
    old_require = v6._require_delta
    v6.MAX_DELTA = MAX_DELTA
    v6._require_delta = _require_delta
    try:
        yield
    finally:
        v6._require_delta = old_require
        v6.MAX_DELTA = old_max


def annulus_derivative_bounds_box_to(
        delta_lo, delta_hi, physical_inner=Fraction(1181, 1000),
        inner=12, outer=32, width=Fraction(1, 2)):
    with _widened_domain():
        return v6.annulus_derivative_bounds_box_to(
            delta_lo, delta_hi, physical_inner, inner, outer, width)


def outer_derivative_bounds_box_to(delta_lo, delta_hi, physical_inner):
    with _widened_domain():
        return v6.outer_derivative_bounds_box_to(
            delta_lo, delta_hi, physical_inner)


def add_outer_derivatives_box_to(series, delta_lo, delta_hi,
                                 physical_inner):
    with _widened_domain():
        return v6.add_outer_derivatives_box_to(
            series, delta_lo, delta_hi, physical_inner)


def direct_moving_band_value_coefficients_from(delta_max, physical_inner):
    with _widened_domain():
        return v6.direct_moving_band_value_coefficients_from(
            delta_max, physical_inner)


def normalized_y_error_from_moment_coefficients(
        delta_max, kd_lower, moment_abs, errors):
    with _widened_domain():
        return v6.normalized_y_error_from_moment_coefficients(
            delta_max, kd_lower, moment_abs, errors)
