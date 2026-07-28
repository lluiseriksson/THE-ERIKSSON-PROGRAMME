"""Byte-separate outer-domain extension registered through delta=0.009."""

from contextlib import contextmanager
from fractions import Fraction
from functools import lru_cache

from flint import arb, arb_series

import surface_remainder_delta0_outer_domain_v3 as v3
from surface_bessel_integral_remainder import aq


MAX_DELTA = Fraction(9, 1000)


def _require_delta(delta_max):
    if not isinstance(delta_max, Fraction):
        raise TypeError("delta_max must be an exact Fraction")
    if not Fraction(0) < delta_max <= MAX_DELTA:
        raise ValueError("v6 outer-domain contract ends at 9/1000")
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
def annulus_derivative_bounds_box_to(
        delta_lo, delta_hi, physical_inner=Fraction(1181, 1000),
        inner=12, outer=32, width=Fraction(1, 2)):
    """V6-local annulus bounds; no older domain cap or cache is reused."""
    if not (isinstance(delta_lo, Fraction)
            and isinstance(delta_hi, Fraction)):
        raise TypeError("delta subbox endpoints must be exact Fractions")
    if not Fraction(1) <= physical_inner <= Fraction(6, 5):
        raise ValueError("physical split must stay inside [1,6/5]")
    if not Fraction(0) <= delta_lo < delta_hi <= MAX_DELTA:
        raise ValueError("delta subbox is outside the v6 contract")
    dlo, dhi = aq(delta_lo), aq(delta_hi)
    w, physical = aq(width), aq(physical_inner)
    lo, hi = int(Fraction(inner)/width), int(Fraction(outer)/width)
    t = v3.v2.hull(arb(0), arb.pi())
    totals = {name: [arb(0) for _ in range(v3.PREC)]
              for name in ("kd", "kf", "hdd", "hdf")}
    for i in range(hi):
        for j in range(hi):
            if i < lo and j < lo:
                continue
            shi, ahi = w*(i+1), w*(j+1)
            cap = min(dhi, (physical/shi)**2, (physical/ahi)**2)
            if not cap > dlo:
                continue
            values = v3.v2.nominal_moment_series(
                v3.v2.hull(dlo, cap), t,
                v3.v2.hull(w*i, shi), v3.v2.hull(w*j, ahi))
            area = 4*w**2
            for name, value in values.items():
                for order, coefficient in enumerate(value.coeffs()):
                    totals[name][order] += area*arb(coefficient.abs_upper())
    return totals


@lru_cache(maxsize=None)
def outer_derivative_bounds_box_to(delta_lo, delta_hi, physical_inner):
    annulus = annulus_derivative_bounds_box_to(
        delta_lo, delta_hi, physical_inner)
    tail = v3.endpoint.derivative_tail_bounds(32)
    return {name: [annulus[name][k]+tail[name][k]
                   for k in range(v3.PREC)] for name in annulus}


def add_outer_derivatives_box_to(series, delta_lo, delta_hi,
                                 physical_inner):
    outer = outer_derivative_bounds_box_to(
        delta_lo, delta_hi, physical_inner)
    result = {}
    for name, value in series.items():
        coefficients = value.coeffs()+[arb(0)]*v3.PREC
        result[name] = arb_series([
            coefficients[k]+outer[name][k]*arb("0 +/- 1")
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
