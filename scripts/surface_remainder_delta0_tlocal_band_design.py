"""T-box-local moving-band majorants for the regular K2 design lane.

This module is deliberately separate from every manifested outer-domain
helper. It replaces only ``cos(t/4)>=1/sqrt(2)`` by the exact lower endpoint
``cos(t_hi/4)`` on one born t box. The remaining positive majorant algebra is
identical to the v2 helper.
"""

from fractions import Fraction
from math import factorial

from flint import arb

import surface_remainder_delta0_derivative_tail as old
import surface_remainder_delta0_outer_domain_v6 as v6
from surface_bessel_integral_remainder import (
    aq, relative_coefficients, upper_gamma_elementary,
)
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_series_design import sinc2_derivatives


def gaussian_rate_from_cmin(cmin: arb) -> arb:
    if not cmin > 0:
        raise ValueError("local Gaussian rate needs cmin>0")
    u = arb("0.6").sin()**2
    sinc = arb("0.6").sin()/arb("0.6")
    return 2*cmin*(1-u)*sinc**2/4


def cmin_from_t_hi(t_hi: arb) -> arb:
    # Arb's independently constructed pi balls overlap but need not satisfy a
    # decidable ``<=`` relation. Accept that endpoint overlap, while rejecting
    # any interval provably below zero or above pi.
    if not t_hi.is_finite() or arb(t_hi.upper()) < 0 or t_hi > arb.pi():
        raise ValueError("born t endpoint must lie in [0,pi]")
    return (t_hi/4).cos()


def radial_tail_at_rate(term: old.Term, radius, rate: arb) -> arb:
    """Four-quadrant integral outside the square at a supplied rate."""
    if not rate > 0:
        raise ValueError("radial tail needs a positive rate")
    s = Fraction(term.p+2, 2)
    z = rate*arb(radius)**2
    gamma = upper_gamma_elementary(s, z)
    radial = gamma/(2*rate**aq(s))
    return 2*arb.pi()*term.c*radial


def moment_majorants(delta_max: Fraction, cmin: arb):
    """The v2 positive algebra with only its c lower bound localized."""
    dmax = v6._require_delta(delta_max)
    global_cmin = arb(2).sqrt()/2
    if cmin < global_cmin:
        raise ValueError("local cmin must imply the global half-line bound")
    u = arb("0.6").sin()**2
    root_lower = (1-2*u).sqrt()
    d = [old.Term(dmax, 0), old.Term(arb(1), 0)] \
        + [old.zero() for _ in range(old.ORDER-1)]
    y = hull(arb(0), arb("0.36"))
    derivatives = sinc2_derivatives(y, old.ORDER)
    p = [old.Term(arb(derivatives[k].abs_upper())
                  / arb(factorial(k)*4**(k+1)), 2*k+2)
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


def direct_moving_band_value_coefficients_from(
        delta_max: Fraction, physical_inner: Fraction, t_hi: arb):
    dmax = v6._require_delta(delta_max)
    if not Fraction(1) <= physical_inner < Fraction(6, 5):
        raise ValueError("value band must leave a nonempty physical rim")
    cmin = cmin_from_t_hi(t_hi)
    rate = gaussian_rate_from_cmin(cmin)
    majorants = moment_majorants(delta_max, cmin)
    exact_radius = aq(physical_inner)*(1/dmax).sqrt()
    scaled_floor = int((10*exact_radius).floor().unique_fmpz())
    radius_lower = Fraction(scaled_floor, 10)
    if not aq(radius_lower) < exact_radius:
        raise AssertionError("physical band radius must be strictly interior")
    out = {}
    for name, series in majorants.items():
        term = series[0]
        threshold = rate/dmax
        assert threshold > aq(Fraction(term.p+2, 2)+5)
        out[name] = radial_tail_at_rate(
            term, aq(radius_lower), rate)/dmax**5
    return radius_lower, out
