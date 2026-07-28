"""Interval modulus for the K4 complex exponential factor.

This is a design probe, not a K4 certificate.  It evaluates the exact
scaled-saddle exponent on a rectangular cover of the registered complex
delta disk and returns an outward upper bound for its real part.  The
rectangular cover is intentionally a superset of the disk; failures are
therefore safe (overly wide), while a pass would only close this modulus
clause.
"""

from __future__ import annotations

from fractions import Fraction
from math import ceil

from flint import acb, arb, ctx


def _interval(lo: Fraction, hi: Fraction) -> arb:
    mid = (arb(lo.numerator) / arb(lo.denominator)
           + arb(hi.numerator) / arb(hi.denominator)) / 2
    radius = (arb(hi.numerator) / arb(hi.denominator)
              - arb(lo.numerator) / arb(lo.denominator)) / 2
    return mid + arb(0, radius)


def _complex_interval(re_lo: Fraction, re_hi: Fraction,
                      im_lo: Fraction, im_hi: Fraction) -> acb:
    return acb(_interval(re_lo, re_hi), _interval(im_lo, im_hi))


def _sinc_square_majorant(x: arb) -> arb:
    root = x.sqrt()
    return (root.sinh() / root) ** 2


def disk_guard(rho: Fraction, radius: Fraction, amplitude: arb) -> arb:
    """Return the strict eta=1-|delta A| guard used by the disk contract."""
    rr = arb(rho.numerator) / arb(rho.denominator)
    R = arb(radius.numerator) / arb(radius.denominator)
    x = rr * R**2 / 4
    p_abs = R**2 / 4 * _sinc_square_majorant(x)
    k = amplitude**2
    delta_a_abs = rr * (2 * p_abs + rr * p_abs**2 / k)
    if not delta_a_abs < 1:
        raise ValueError("complex disk admits |delta*A| >= 1")
    return 1 - delta_a_abs


def _exponent(delta: acb, sigma: acb, tau: acb, phi: acb,
              t: arb, mirror: bool) -> acb:
    c = (t / 4).cos()
    s4 = (t / 4).sin()
    reference = s4 if mirror else c
    root_delta = delta.sqrt()
    s = root_delta * sigma
    alpha = root_delta * tau
    if mirror:
        p = (s / 2).cos() ** 2
        q = (alpha / 2).cos() ** 2
    else:
        p = (s / 2).sin() ** 2
        q = (alpha / 2).sin() ** 2
    r2 = 4 * c**2 * (1 - p) * (1 - q) + 4 * s4**2 * p * q
    ratio = r2 / (4 * reference**2)
    root_ratio = ratio.sqrt()
    z = root_delta * phi / 2
    S = phi**2 / 2 * z.sinc()**2
    return -4 * reference * root_ratio * S


def exponent_real_upper(*, t: Fraction = Fraction(29, 10),
                        rho: Fraction = Fraction(7, 100),
                        radius: Fraction = Fraction(4),
                        phi_max: Fraction | None = None,
                        delta_splits: int = 4,
                        spatial_splits: int = 2,
                        phi_splits: int = 16,
                        mirror: bool = False) -> arb:
    """Enclose the maximum real exponent over a rectangular cover."""
    if min(delta_splits, spatial_splits, phi_splits) < 1:
        raise ValueError("split counts must be positive")
    ctx.prec = max(ctx.prec, 140)
    t_arb = arb(t.numerator) / arb(t.denominator)
    rho_q = rho
    R_q = radius
    phi_q = phi_max if phi_max is not None else Fraction(12566371, 1_000_000)
    amplitude = (t_arb / 4).sin() if mirror else (t_arb / 4).cos()
    disk_guard(rho_q, R_q, amplitude)
    best = None
    for i in range(delta_splits):
        re_lo = -rho_q + 2 * rho_q * i / delta_splits
        re_hi = -rho_q + 2 * rho_q * (i + 1) / delta_splits
        for j in range(delta_splits):
            im_lo = -rho_q + 2 * rho_q * j / delta_splits
            im_hi = -rho_q + 2 * rho_q * (j + 1) / delta_splits
            delta = _complex_interval(re_lo, re_hi, im_lo, im_hi)
            for k in range(spatial_splits):
                s_lo = -R_q + 2 * R_q * k / spatial_splits
                s_hi = -R_q + 2 * R_q * (k + 1) / spatial_splits
                for ell in range(spatial_splits):
                    a_lo = -R_q + 2 * R_q * ell / spatial_splits
                    a_hi = -R_q + 2 * R_q * (ell + 1) / spatial_splits
                    sigma = acb(_interval(s_lo, s_hi), 0)
                    tau = acb(_interval(a_lo, a_hi), 0)
                    for q in range(phi_splits):
                        p_lo = phi_q * q / phi_splits
                        p_hi = phi_q * (q + 1) / phi_splits
                        phi = acb(_interval(p_lo, p_hi), 0)
                        value = _exponent(delta, sigma, tau, phi,
                                          t_arb, mirror)
                        upper = value.real.upper()
                        if not upper.is_finite():
                            raise ArithmeticError("non-finite real exponent enclosure")
                        best = upper if best is None else max(best, upper)
    assert best is not None
    return arb(best)


def exponent_real_upper_polar(*, t: Fraction = Fraction(29, 10),
                              rho: Fraction = Fraction(7, 100),
                              radius: Fraction = Fraction(4),
                              phi_max: Fraction | None = None,
                              radial_splits: int = 4,
                              angular_splits: int = 16,
                              spatial_splits: int = 2,
                              phi_splits: int = 16,
                              mirror: bool = False) -> arb:
    """Same enclosure using a polar superset of the complex disk."""
    if min(radial_splits, angular_splits, spatial_splits, phi_splits) < 1:
        raise ValueError("split counts must be positive")
    ctx.prec = max(ctx.prec, 140)
    t_arb = arb(t.numerator) / arb(t.denominator)
    phi_q = phi_max if phi_max is not None else Fraction(12566371, 1_000_000)
    amplitude = (t_arb / 4).sin() if mirror else (t_arb / 4).cos()
    disk_guard(rho, radius, amplitude)
    two_pi_up = Fraction(6283186, 1_000_000)
    best = None
    for i in range(radial_splits):
        r_lo = rho * i / radial_splits
        r_hi = rho * (i + 1) / radial_splits
        r = _interval(r_lo, r_hi)
        for j in range(angular_splits):
            a_lo = two_pi_up * j / angular_splits
            a_hi = two_pi_up * (j + 1) / angular_splits
            angle = _interval(a_lo, a_hi)
            delta = acb(r * angle.cos(), r * angle.sin())
            for k in range(spatial_splits):
                s_lo = -radius + 2 * radius * k / spatial_splits
                s_hi = -radius + 2 * radius * (k + 1) / spatial_splits
                for ell in range(spatial_splits):
                    a0_lo = -radius + 2 * radius * ell / spatial_splits
                    a0_hi = -radius + 2 * radius * (ell + 1) / spatial_splits
                    sigma = acb(_interval(s_lo, s_hi), 0)
                    tau = acb(_interval(a0_lo, a0_hi), 0)
                    for q in range(phi_splits):
                        p_lo = phi_q * q / phi_splits
                        p_hi = phi_q * (q + 1) / phi_splits
                        phi = acb(_interval(p_lo, p_hi), 0)
                        value = _exponent(delta, sigma, tau, phi,
                                          t_arb, mirror)
                        upper = value.real.upper()
                        if not upper.is_finite():
                            raise ArithmeticError("non-finite polar enclosure")
                        best = upper if best is None else max(best, upper)
    assert best is not None
    return arb(best)


def modulus_upper(exponent_upper: arb, t: Fraction = Fraction(29, 10),
                  phi_max: Fraction | None = None) -> arb:
    phi_q = phi_max if phi_max is not None else Fraction(12566371, 1_000_000)
    phi = arb(phi_q.numerator) / arb(phi_q.denominator)
    c = (arb(t.numerator) / arb(t.denominator) / 4).cos()
    # The factor 4*c is already included in _exponent; retain the same
    # prefactor as the historical reach judge.
    return arb.pi() * phi * exponent_upper.exp()


__all__ = ["disk_guard", "exponent_real_upper", "exponent_real_upper_polar",
           "modulus_upper"]
