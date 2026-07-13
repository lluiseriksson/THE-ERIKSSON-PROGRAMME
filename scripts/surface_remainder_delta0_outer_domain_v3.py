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


@lru_cache(maxsize=None)
def annulus_derivative_bounds_box(delta_lo, delta_hi, inner=12, outer=32,
                                  width=Fraction(1, 2)):
    """Annulus derivative majorants on one exact delta subbox."""
    if not (isinstance(delta_lo, Fraction)
            and isinstance(delta_hi, Fraction)):
        raise TypeError("delta subbox endpoints must be Fractions")
    if not Fraction(0) <= delta_lo < delta_hi <= MAX_DELTA:
        raise ValueError("delta subbox is outside the v3 contract")
    dlo, dhi = aq(delta_lo), aq(delta_hi)
    w = aq(width)
    lo, hi = int(Fraction(inner)/width), int(Fraction(outer)/width)
    physical_inner = arb(1)
    t = v2.hull(arb(0), arb.pi())
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("kd", "kf", "hdd", "hdf")}
    for i in range(hi):
        for j in range(hi):
            if i < lo and j < lo:
                continue
            shi, ahi = w*(i+1), w*(j+1)
            cap = min(dhi, (physical_inner/shi)**2,
                      (physical_inner/ahi)**2)
            if not cap > dlo:
                continue
            values = v2.nominal_moment_series(
                v2.hull(dlo, cap), t,
                v2.hull(w*i, shi), v2.hull(w*j, ahi))
            area = 4*w**2
            for name, value in values.items():
                for order, coefficient in enumerate(value.coeffs()):
                    totals[name][order] += area*arb(coefficient.abs_upper())
    return totals


@lru_cache(maxsize=None)
def outer_derivative_bounds_box(delta_lo, delta_hi):
    annulus = annulus_derivative_bounds_box(delta_lo, delta_hi)
    tail = endpoint.derivative_tail_bounds(32)
    return {name: [annulus[name][k]+tail[name][k]
                   for k in range(PREC)] for name in annulus}


def add_outer_derivatives_box(series, delta_lo, delta_hi):
    outer = outer_derivative_bounds_box(delta_lo, delta_hi)
    result = {}
    for name, value in series.items():
        coefficients = value.coeffs()+[arb(0)]*PREC
        result[name] = arb_series([
            coefficients[k]+outer[name][k]*arb("0 +/- 1")
            for k in range(PREC)
        ], PREC)
    return result


def direct_moving_band_value_coefficients(delta_max):
    dmax = _require_delta(delta_max)
    with _registered_domain():
        majorants = v2.moment_majorants(delta_max)
    scaled_floor = int((10*(1/dmax).sqrt()).floor().unique_fmpz())
    radius_lower = Fraction(scaled_floor, 10)
    if not aq(radius_lower) < (1/dmax).sqrt():
        raise AssertionError("decimal band radius must be strictly interior")
    threshold = endpoint.gaussian_rate()/dmax
    out = {}
    for name, series in majorants.items():
        term = series[0]
        assert threshold > aq(Fraction(term.p+2, 2)+5)
        out[name] = endpoint.radial_tail(term, aq(radius_lower))/dmax**5
    return radius_lower, out


def normalized_y_error_from_moment_coefficients(
        delta_max, kd_lower, moment_abs, error_coefficients):
    _require_delta(delta_max)
    with _registered_domain():
        return v2.normalized_y_error_from_moment_coefficients(
            delta_max, kd_lower, moment_abs, error_coefficients)
