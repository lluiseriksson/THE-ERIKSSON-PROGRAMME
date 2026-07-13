"""Delta-parameterized outer-domain bounds for regular K2 extensions.

This module leaves the manifested endpoint helper byte-invariant.  Unlike
that endpoint-only implementation, every public entry point here requires an
explicit rational ``delta_max`` and propagates it through the annulus and the
moving physical-band majorants.
"""

from fractions import Fraction
from functools import lru_cache
from math import factorial

from flint import arb, arb_series

import surface_remainder_delta0_derivative_tail as old
from surface_bessel_integral_remainder import aq, relative_coefficients
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_series_design import (
    PREC, nominal_moment_series, sinc2_derivatives,
)


def _require_delta(delta_max):
    if not isinstance(delta_max, Fraction):
        raise TypeError("delta_max must be an exact Fraction")
    if not Fraction(0) < delta_max <= Fraction(1, 200):
        raise ValueError("v2 outer-domain design is registered only to 1/200")
    return aq(delta_max)


def moment_majorants(delta_max):
    """Endpoint majorant algebra with its constant delta lane enlarged."""
    dmax = _require_delta(delta_max)
    cmin = arb(2).sqrt()/2
    u = arb("0.6").sin()**2
    root_lower = (1-2*u).sqrt()
    d = [old.Term(dmax, 0), old.Term(arb(1), 0)] \
        +[old.zero() for _ in range(old.ORDER-1)]
    y = hull(arb(0), arb("0.36"))
    derivatives = sinc2_derivatives(y, old.ORDER)
    p = [old.Term(arb(derivatives[k].abs_upper())
                  /arb(factorial(k)*4**(k+1)), 2*k+2)
         for k in range(old.ORDER+1)]
    q = list(p)
    pq = old.mul(p, q)
    w = old.add(old.add(p, q), old.scale(old.mul(d, pq), arb(2)))
    radicand = old.add(old.const(1), old.scale(old.mul(d, w), arb(1)))
    root = old.sqrt_series(radicand, root_lower)
    root_inv = old.inv(root, root_lower)
    one_plus_root_inv = old.inv(old.add(old.const(1), root), 1+root_lower)
    phase = old.scale(old.mul(w, one_plus_root_inv), arb(4))
    exponential = old.exp_relative(phase)
    h = old.scale(old.mul(d, root_inv), 1/(4*cmin))
    a_poly = old.polynomial(h, relative_coefficients("A", 4))
    b_poly = old.polynomial(h, relative_coefficients("B", 4))
    root_half_inv = old.inv(
        old.sqrt_series(root, root_lower.sqrt()), root_lower.sqrt())
    root_3half_inv = old.mul(root_inv, root_half_inv)
    root_5half_inv = old.mul(old.mul(root_inv, root_inv), root_half_inv)
    psum = old.add(p, q)
    d_weight = old.scale(old.add(old.const(1), old.mul(d, psum)), arb(2))
    bracket = old.add(old.const(3), old.add(
        old.scale(old.mul(d, p), arb(3)),
        old.add(old.scale(old.mul(d, q), arb(3)),
                old.scale(old.mul(old.mul(d, d), pq), arb(2)))))
    f_over = old.scale(old.mul(p, bracket), arb(4))
    common = 1/(2*arb.pi()).sqrt()
    kernel = old.scale(old.mul(root_3half_inv, a_poly),
                       2*common/(4*cmin)**(arb(3)/2))
    hregular = old.scale(old.mul(root_5half_inv, b_poly),
                         common/(4*cmin)**(arb(5)/2))
    return {
        "kd": old.mul(old.mul(kernel, d_weight), exponential),
        "kf": old.mul(old.mul(kernel, f_over), exponential),
        "hdd": old.mul(old.mul(hregular, old.mul(d_weight, d_weight)),
                       exponential),
        "hdf": old.mul(old.mul(hregular, old.mul(d_weight, f_over)),
                       exponential),
    }


@lru_cache(maxsize=None)
def annulus_derivative_bounds(delta_max, inner=12, outer=32,
                              width=Fraction(1, 2)):
    """Uniform derivatives on the annulus with an explicit delta cap."""
    dmax = _require_delta(delta_max)
    w = aq(width)
    lo, hi = int(Fraction(inner)/width), int(Fraction(outer)/width)
    physical_inner = arb(1)
    t = hull(arb(0), arb.pi())
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("kd", "kf", "hdd", "hdf")}
    for i in range(hi):
        for j in range(hi):
            if i < lo and j < lo:
                continue
            shi, ahi = w*(i+1), w*(j+1)
            cap = min(dmax, (physical_inner/shi)**2,
                      (physical_inner/ahi)**2)
            values = nominal_moment_series(
                hull(arb(0), cap), t,
                hull(w*i, shi), hull(w*j, ahi))
            area = 4*w**2
            for name, value in values.items():
                for order, coefficient in enumerate(value.coeffs()):
                    totals[name][order] += area*arb(coefficient.abs_upper())
    return totals


def moving_band_value_coefficients(delta_max):
    """Return e_M with the complete moving band bounded by e_M*delta^5."""
    dmax = _require_delta(delta_max)
    majorants = moment_majorants(delta_max)
    threshold = old.gaussian_rate()/dmax
    radius_lower = int((1/dmax).sqrt().floor().unique_fmpz())
    if not arb(radius_lower) < (1/dmax).sqrt():
        raise AssertionError("moving-band radius must be strictly interior")
    out = {}
    for name, series in majorants.items():
        assert all(threshold > aq(Fraction(term.p+2, 2)+5)
                   for term in series[:5])
        missing = sum((
            old.radial_tail(term, radius_lower)*dmax**(order-5)
            for order, term in enumerate(series[:5])
        ), arb(0))
        remainder = old.radial_tail(series[5], radius_lower)
        out[name] = missing+remainder
    return radius_lower, out


def direct_moving_band_value_coefficients(delta_max):
    """Direct value-only band charge e_M with |M_band| <= e_M*delta^5.

    The transition band is deliberately not differentiated.  The zeroth
    majorant bounds its actual value uniformly after all positive absolute
    algebra is evaluated at ``delta_max``.  For a term rho^p exp(-a rho^2),
    the radial tail divided by delta^5 is increasing while
    a/delta > (p+2)/2+5; the asserted inequality puts its maximum at the
    registered endpoint.  Bounding the band by the entire exterior of
    rho=1/sqrt(delta) and rounding that radius down remains conservative.
    """
    dmax = _require_delta(delta_max)
    majorants = moment_majorants(delta_max)
    threshold = old.gaussian_rate()/dmax
    radius_lower = int((1/dmax).sqrt().floor().unique_fmpz())
    out = {}
    for name, series in majorants.items():
        term = series[0]
        assert threshold > aq(Fraction(term.p+2, 2)+5)
        out[name] = old.radial_tail(term, radius_lower)/dmax**5
    return radius_lower, out


@lru_cache(maxsize=None)
def outer_derivative_bounds(delta_max):
    annulus = annulus_derivative_bounds(delta_max)
    tail = old.derivative_tail_bounds(32)
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
