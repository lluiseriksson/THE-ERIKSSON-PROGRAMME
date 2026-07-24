"""R6-only outer-domain wrapper with adaptive delta-base subdivision.

The v6 annulus helper can lose the nonzero leading-term guard when a broad
delta interval starts at zero.  Splitting that interval and summing absolute
coefficient bounds is a valid (conservative) union majorant; evaluating only
at delta=0 would be an invalid underbound and is intentionally not used.
"""

from functools import lru_cache
from fractions import Fraction

from flint import arb, arb_series

import surface_remainder_delta0_outer_domain_v7 as v7
import surface_remainder_delta0_outer_domain_v3 as v3
import surface_remainder_delta0_outer_domain_v6 as v6
import surface_remainder_delta0_band_gap_design as band_gap


MAX_DELTA = Fraction(1, 100)
MAX_DEPTH = 12


def _validate(delta_lo, delta_hi):
    if not (isinstance(delta_lo, Fraction)
            and isinstance(delta_hi, Fraction)):
        raise TypeError("delta endpoints must be exact Fractions")
    if not Fraction(0) <= delta_lo < delta_hi <= MAX_DELTA:
        raise ValueError("R6 split wrapper ends at 1/100")


def _sum_series_bounds(total, value):
    for name, series in value.items():
        for order, coefficient in enumerate(series.coeffs()):
            total[name][order] += arb(coefficient.abs_upper())


def _split_nominal(base_lo, base_hi, t, sigma, tau, total, depth=0):
    base = v3.v2.hull(base_lo, base_hi)
    try:
        value = v3.v2.nominal_moment_series(base, t, sigma, tau)
    except ValueError as exc:
        if "leading term in denominator" not in str(exc):
            raise
        if depth >= MAX_DEPTH:
            raise RuntimeError(
                "R6 delta subdivision exhausted at %s:%s" %
                (base_lo, base_hi)) from exc
        mid = (base_lo+base_hi)/2
        if not mid > base_lo or not base_hi > mid:
            raise
        _split_nominal(base_lo, mid, t, sigma, tau, total, depth+1)
        _split_nominal(mid, base_hi, t, sigma, tau, total, depth+1)
        return
    _sum_series_bounds(total, value)


@lru_cache(maxsize=None)
def annulus_derivative_bounds_box_to(
        delta_lo, delta_hi, physical_inner=Fraction(1181, 1000),
        inner=12, outer=32, width=Fraction(1, 2)):
    _validate(delta_lo, delta_hi)
    if not Fraction(1) <= physical_inner <= Fraction(6, 5):
        raise ValueError("physical split outside [1,6/5]")
    dlo, dhi = v3.v2.aq(delta_lo), v3.v2.aq(delta_hi)
    w, physical = v3.v2.aq(width), v3.v2.aq(physical_inner)
    lo, hi = int(Fraction(inner)/width), int(Fraction(outer)/width)
    t = v3.v2.hull(arb(0), arb.pi())
    total = {name: [arb(0) for _ in range(v3.PREC)]
             for name in ("kd", "kf", "hdd", "hdf")}
    for i in range(hi):
        for j in range(hi):
            if i < lo and j < lo:
                continue
            shi, ahi = w*(i+1), w*(j+1)
            cap = min(dhi, (physical/shi)**2, (physical/ahi)**2)
            if not cap > dlo:
                continue
            local = {name: [arb(0) for _ in range(v3.PREC)]
                     for name in ("kd", "kf", "hdd", "hdf")}
            _split_nominal(dlo, cap, t, v3.v2.hull(w*i, shi),
                           v3.v2.hull(w*j, ahi), local)
            area = 4*w**2
            for name, row in local.items():
                for order, coefficient in enumerate(row):
                    total[name][order] += area*coefficient
    return total


@lru_cache(maxsize=None)
def annulus_derivative_bounds_box_to_t(
        delta_lo, delta_hi, physical_inner=Fraction(1181, 1000),
        t_lo=Fraction(0), t_hi=Fraction(31415927, 10000000),
        inner=12, outer=32, width=Fraction(1, 2)):
    """Annulus majorant using the local t-box rather than [0, pi].

    This keeps outward rounding and the same spatial/tail domain while
    avoiding the global t-hull used by the original design helper.
    """
    _validate(delta_lo, delta_hi)
    if not (isinstance(t_lo, Fraction) and isinstance(t_hi, Fraction)
            and t_lo < t_hi):
        raise TypeError("t endpoints must be exact Fractions")
    if not (Fraction(0) <= t_lo and t_hi <= Fraction(31415927, 10000000)):
        raise ValueError("t box outside certified [0, pi] proxy")
    if not Fraction(1) <= physical_inner <= Fraction(6, 5):
        raise ValueError("physical split outside [1,6/5]")
    dlo, dhi = v3.v2.aq(delta_lo), v3.v2.aq(delta_hi)
    w, physical = v3.v2.aq(width), v3.v2.aq(physical_inner)
    lo, hi = int(Fraction(inner)/width), int(Fraction(outer)/width)
    t = v3.v2.hull(v3.v2.aq(t_lo), v3.v2.aq(t_hi))
    total = {name: [arb(0) for _ in range(v3.PREC)]
             for name in ("kd", "kf", "hdd", "hdf")}
    for i in range(hi):
        for j in range(hi):
            if i < lo and j < lo:
                continue
            shi, ahi = w*(i+1), w*(j+1)
            cap = min(dhi, (physical/shi)**2, (physical/ahi)**2)
            if not cap > dlo:
                continue
            local = {name: [arb(0) for _ in range(v3.PREC)]
                     for name in ("kd", "kf", "hdd", "hdf")}
            _split_nominal(dlo, cap, t, v3.v2.hull(w*i, shi),
                           v3.v2.hull(w*j, ahi), local)
            area = 4*w**2
            for name, row in local.items():
                for order, coefficient in enumerate(row):
                    total[name][order] += area*coefficient
    return total


@lru_cache(maxsize=None)
def outer_derivative_bounds_box_to(delta_lo, delta_hi, physical_inner):
    annulus = annulus_derivative_bounds_box_to(
        delta_lo, delta_hi, physical_inner)
    tail = v3.endpoint.derivative_tail_bounds(32)
    return {name: [annulus[name][k]+tail[name][k]
                   for k in range(v3.PREC)] for name in annulus}


@lru_cache(maxsize=None)
def outer_derivative_bounds_box_to_t(delta_lo, delta_hi, physical_inner,
                                     t_lo, t_hi):
    annulus = annulus_derivative_bounds_box_to_t(
        delta_lo, delta_hi, physical_inner, t_lo, t_hi)
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


def add_outer_derivatives_box_to_t(series, delta_lo, delta_hi,
                                   physical_inner, t_lo, t_hi):
    """Local-t counterpart used only by diagnostic R6 probes."""
    outer = outer_derivative_bounds_box_to_t(
        delta_lo, delta_hi, physical_inner, t_lo, t_hi)
    result = {}
    for name, value in series.items():
        coefficients = value.coeffs()+[arb(0)]*v3.PREC
        result[name] = arb_series([
            coefficients[k]+outer[name][k]*arb("0 +/- 1")
            for k in range(v3.PREC)], v3.PREC)
    return result


def direct_moving_band_value_coefficients_from(delta_max, physical_inner,
                                               t_hi=None):
    """Use the nonzero physical-deficit rate on one born t-box.

    The t-local rate is strictly sharper than the half-line c>=1/sqrt(2)
    rate.  The v6 domain guard is widened only for this isolated call and is
    restored before return.
    """
    old_max, old_require = v6.MAX_DELTA, v6._require_delta
    v6.MAX_DELTA = MAX_DELTA
    v6._require_delta = lambda value: v6.aq(value)
    try:
        if t_hi is None:
            return v7.direct_moving_band_value_coefficients_from(
                delta_max, physical_inner)
        return band_gap.direct_moving_band_value_coefficients_from(
            delta_max, physical_inner, t_hi)
    finally:
        v6._require_delta, v6.MAX_DELTA = old_require, old_max


def normalized_y_error_from_moment_coefficients(
        delta_max, kd_lower, moment_abs, errors):
    return v7.normalized_y_error_from_moment_coefficients(
        delta_max, kd_lower, moment_abs, errors)
