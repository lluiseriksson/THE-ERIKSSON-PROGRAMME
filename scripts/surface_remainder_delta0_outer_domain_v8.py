"""Byte-separate outer-domain wrapper for the preregistered K2 0125 probe.

This widens only the checked domain cap of the unchanged v6 implementation to
``1/80``.  It is a design prerequisite, not a certificate or theorem load.
"""

from contextlib import contextmanager
from fractions import Fraction

import surface_remainder_delta0_outer_domain_v6 as v6


MAX_DELTA = Fraction(1, 80)


def _require_delta(delta_max):
    if not isinstance(delta_max, Fraction):
        raise TypeError("delta_max must be an exact Fraction")
    if not Fraction(0) < delta_max <= MAX_DELTA:
        raise ValueError("v8 outer-domain contract ends at 1/80")
    return v6.aq(delta_max)


@contextmanager
def _widened_domain():
    old_max, old_require = v6.MAX_DELTA, v6._require_delta
    v6.MAX_DELTA, v6._require_delta = MAX_DELTA, _require_delta
    try:
        yield
    finally:
        v6._require_delta, v6.MAX_DELTA = old_require, old_max


def annulus_derivative_bounds_box_to(delta_lo, delta_hi,
                                     physical_inner=Fraction(1181, 1000),
                                     inner=12, outer=32,
                                     width=Fraction(1, 2)):
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
