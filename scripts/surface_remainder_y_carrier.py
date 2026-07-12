"""Exact delta/spatial jets for the five raw moments defining Y=X/delta.

Near removable z=0 corners the Bessel quotients are evaluated as entire
functions of w=z^2. Away from them the completely-monotone scaled lane is
used. This module provides integrands only; S2 certification remains separate.
"""

from __future__ import annotations

from math import factorial

import mpmath as mp
from flint import arb

from surface_remainder_arb_jet2 import hull
from surface_remainder_centered_prefactor import (
    A,
    Dual,
    Jet,
    dadd,
    dmul,
    dsquare,
    dual,
    jadd,
    jexp,
    jinv,
    jmul,
    jneg,
    jscale,
    jsin,
    jcos,
    jsqrt,
    jsquare,
    jet,
    outer_jet,
    unary,
)
from surface_remainder_core_l2_arb import cutoff_dual


RAW_NAMES = ("K", "KD", "KF", "HDD", "HDF")


def _falling(k: int, order: int) -> int:
    out = 1
    for value in range(k - order + 1, k + 1):
        out *= value
    return out if k >= order else 0


def _coefficient(k: int, family: str) -> arb:
    if family == "G":
        return arb(1) / (arb(2) * arb(4) ** k * factorial(k) * factorial(k + 1))
    if family == "H":
        return arb(1) / (arb(4) ** (k + 1) * factorial(k) * factorial(k + 2))
    raise ValueError(family)


def entire_w_derivatives(w: arb, family: str, terms: int = 24) -> list[arb]:
    """Orders 0..4 of G(sqrt(w)) or H(sqrt(w)), with explicit tails."""

    if w.lower() < 0:
        w = hull(arb(0), arb(w.abs_upper()))
    wmax = arb(w.abs_upper())
    sums = [arb(0) for _ in range(5)]
    for k in range(terms):
        coefficient = _coefficient(k, family)
        for order in range(5):
            falling = _falling(k, order)
            if falling:
                sums[order] += coefficient * falling * w ** (k - order)
    for order in range(5):
        k = max(terms, order)
        first = _coefficient(k, family) * _falling(k, order) * wmax ** (k - order)
        second = (
            _coefficient(k + 1, family)
            * _falling(k + 1, order)
            * wmax ** (k + 1 - order)
        )
        ratio = second / first
        if not bool(ratio < arb(1) / 2):
            raise ValueError("entire-series tail ratio is not contractive")
        sums[order] += hull(arb(0), first / (1 - ratio))
    return sums


def _outer_w_jet(w: Jet, family: str) -> Jet:
    derivatives = entire_w_derivatives(w.c0.v, family)
    f0 = unary(w.c0, derivatives[0], derivatives[1], derivatives[2])
    f1 = unary(w.c0, derivatives[1], derivatives[2], derivatives[3])
    f2 = unary(w.c0, derivatives[2], derivatives[3], derivatives[4])
    return Jet(
        f0,
        dmul(f1, w.c1),
        dadd(dmul(f1, w.c2), dmul(f2, dmul(dsquare(w.c1), A(1) / 2))),
    )


def _bessel_and_exponential(
    beta: Jet, beta2: Jet, radius2: Jet, reference: arb | Jet
) -> tuple[Jet, Jet, Jet]:
    w = jscale(jmul(beta2, radius2), 4)
    w_upper = w.c0.v.upper()
    w_lower = w.c0.v.lower()
    if w_upper <= 25:
        g = _outer_w_jet(w, "G")
        h = _outer_w_jet(w, "H")
        reference_jet = reference if isinstance(reference, Jet) else jet(reference)
        phase = jscale(jmul(beta, reference_jet), -4)
        return g, h, phase
    if w_lower > 16:
        z = jsqrt(w)
        reference_jet = reference if isinstance(reference, Jet) else jet(reference)
        phase = jadd(z, jscale(jmul(beta, reference_jet), -4))
        return outer_jet(z, "A"), outer_jet(z, "B"), phase
    raise ValueError("Bessel lane transition box must subdivide")


def raw_integrand_parts(
    delta_value: arb, t_value: arb, s: Dual, alpha: Dual
) -> tuple[dict[str, Jet], Jet]:
    delta = Jet(dual(delta_value), dual(1), dual(0))
    beta = jinv(delta)
    beta2 = jsquare(beta)
    beta_sqrt = jsqrt(beta)
    beta32, beta52 = jmul(beta, beta_sqrt), jmul(beta2, beta_sqrt)
    sj, aj = jet(s), jet(alpha)
    c, s4 = (t_value / 4).cos(), (t_value / 4).sin()
    ps = jsquare(jsin(jscale(sj, A(1) / 2)))
    pa = jsquare(jsin(jscale(aj, A(1) / 2)))
    one = jet(1)
    radius2 = jadd(
        jscale(jmul(jadd(one, jneg(ps)), jadd(one, jneg(pa))), 4 * c**2),
        jscale(jmul(ps, pa), 4 * s4**2),
    )
    g, h, phase = _bessel_and_exponential(beta, beta2, radius2, c)
    kernel = jmul(jscale(beta52, 2), g)
    hb = jmul(beta32, h)
    d = jscale(jadd(one, jneg(jadd(ps, pa))), 2)
    cc = 2 * c**2 - 1
    cos_s, cos_a = jcos(sj), jcos(aj)
    n = jadd(
        jscale(jcos(jscale(sj, 2)), cc),
        jmul(cos_a, jadd(jscale(cos_s, cc), jadd(jet(-1), jsquare(cos_s)))),
    )
    f = jadd(n, jscale(d, -cc))
    return {
        "K": kernel,
        "KD": jmul(kernel, d),
        "KF": jmul(kernel, f),
        "HDD": jmul(hb, jsquare(d)),
        "HDF": jmul(hb, jmul(d, f)),
    }, phase


def raw_integrand_jets(
    delta_value: arb, t_value: arb, s: Dual, alpha: Dual
) -> dict[str, Jet]:
    prefactors, phase = raw_integrand_parts(delta_value, t_value, s, alpha)
    exponential = jexp(phase)
    return {name: jmul(prefactor, exponential)
            for name, prefactor in prefactors.items()}


def raw_integrand_parts_t(
    delta_value: arb, t_value: arb, s: Dual, alpha: Dual
) -> tuple[dict[str, Jet], Jet]:
    """The same five raw moments, with Jet derivatives taken in t."""

    delta = Jet(dual(delta_value), dual(0), dual(0))
    beta = jinv(delta)
    beta2 = jsquare(beta)
    beta_sqrt = jsqrt(beta)
    beta32, beta52 = jmul(beta, beta_sqrt), jmul(beta2, beta_sqrt)
    tj = Jet(dual(t_value), dual(1), dual(0))
    c = jcos(jscale(tj, A(1) / 4))
    s4 = jsin(jscale(tj, A(1) / 4))
    sj, aj = jet(s), jet(alpha)
    ps = jsquare(jsin(jscale(sj, A(1) / 2)))
    pa = jsquare(jsin(jscale(aj, A(1) / 2)))
    one = jet(1)
    radius2 = jadd(
        jmul(jscale(jmul(jadd(one, jneg(ps)), jadd(one, jneg(pa))), 4),
             jsquare(c)),
        jmul(jscale(jmul(ps, pa), 4), jsquare(s4)),
    )
    g, h, phase = _bessel_and_exponential(beta, beta2, radius2, c)
    kernel = jmul(jscale(beta52, 2), g)
    hb = jmul(beta32, h)
    d = jscale(jadd(one, jneg(jadd(ps, pa))), 2)
    cc = jadd(jscale(jsquare(c), 2), jet(-1))
    cos_s, cos_a = jcos(sj), jcos(aj)
    n = jadd(
        jmul(jcos(jscale(sj, 2)), cc),
        jmul(cos_a, jadd(jmul(cos_s, cc),
                         jadd(jet(-1), jsquare(cos_s)))),
    )
    f = jadd(n, jneg(jmul(cc, d)))
    return {
        "K": kernel,
        "KD": jmul(kernel, d),
        "KF": jmul(kernel, f),
        "HDD": jmul(hb, jsquare(d)),
        "HDF": jmul(hb, jmul(d, f)),
    }, phase


def raw_integrand_jets_t(
    delta_value: arb, t_value: arb, s: Dual, alpha: Dual
) -> dict[str, Jet]:
    prefactors, phase = raw_integrand_parts_t(
        delta_value, t_value, s, alpha
    )
    exponential = jexp(phase)
    return {name: jmul(prefactor, exponential)
            for name, prefactor in prefactors.items()}


def scaled_raw_integrand_parts(
    delta_value: arb, t_value: arb, sigma: Dual, tau: Dual,
    localized: bool = True,
) -> tuple[dict[str, Jet], Jet]:
    """Main-saddle raw moments after s=sqrt(delta)sigma, with Jacobian/cutoff."""

    delta = Jet(dual(delta_value), dual(1), dual(0))
    beta = jinv(delta)
    beta2 = jsquare(beta)
    beta_sqrt = jsqrt(beta)
    beta32, beta52 = jmul(beta, beta_sqrt), jmul(beta2, beta_sqrt)
    root_delta = jsqrt(delta)
    sj, aj = jmul(root_delta, jet(sigma)), jmul(root_delta, jet(tau))
    c, s4 = (t_value / 4).cos(), (t_value / 4).sin()
    ps = jsquare(jsin(jscale(sj, A(1) / 2)))
    pa = jsquare(jsin(jscale(aj, A(1) / 2)))
    one = jet(1)
    radius2 = jadd(
        jscale(jmul(jadd(one, jneg(ps)), jadd(one, jneg(pa))), 4 * c**2),
        jscale(jmul(ps, pa), 4 * s4**2),
    )
    z = jscale(jmul(beta, jsqrt(radius2)), 2)
    if z.c0.v.lower() <= 4:
        raise ValueError("scaled raw support requires z>4; subdivide or use entire lane")
    g, h = outer_jet(z, "A"), outer_jet(z, "B")
    phase = jadd(z, jscale(beta, -4 * c))
    kernel = jmul(jscale(beta52, 2), g)
    hb = jmul(beta32, h)
    d = jscale(jadd(one, jneg(jadd(ps, pa))), 2)
    cc = 2 * c**2 - 1
    cos_s, cos_a = jcos(sj), jcos(aj)
    n = jadd(
        jscale(jcos(jscale(sj, 2)), cc),
        jmul(cos_a, jadd(jscale(cos_s, cc), jadd(jet(-1), jsquare(cos_s)))),
    )
    f = jadd(n, jscale(d, -cc))
    cutoff = jet(cutoff_dual(sigma, tau)) if localized else jet(1)
    jacobian_cutoff = jmul(delta, cutoff)
    return {
        "K": jmul(jacobian_cutoff, kernel),
        "KD": jmul(jacobian_cutoff, jmul(kernel, d)),
        "KF": jmul(jacobian_cutoff, jmul(kernel, f)),
        "HDD": jmul(jacobian_cutoff, jmul(hb, jsquare(d))),
        "HDF": jmul(jacobian_cutoff, jmul(hb, jmul(d, f))),
    }, phase


def scaled_raw_integrand_parts_fixed_square(
    delta_value: arb, t_value: arb, sigma: Dual, tau: Dual
) -> tuple[dict[str, Jet], Jet]:
    """Scaled main-saddle moments without the localization cutoff."""
    return scaled_raw_integrand_parts(
        delta_value, t_value, sigma, tau, localized=False
    )


def scalar_raw(
    delta: mp.mpf, t: mp.mpf, s: mp.mpf, alpha: mp.mpf, name: str
) -> mp.mpf:
    beta = 1 / delta
    c, s4 = mp.cos(t / 4), mp.sin(t / 4)
    p, q = mp.sin(s / 2) ** 2, mp.sin(alpha / 2) ** 2
    radius = mp.sqrt(4 * c**2 * (1 - p) * (1 - q) + 4 * s4**2 * p * q)
    z = 2 * beta * radius
    g = mp.besseli(1, z) / z if z else mp.mpf("0.5")
    h = mp.besseli(2, z) / z**2 if z else mp.mpf("0.125")
    kernel = 2 * beta**mp.mpf("2.5") * g * mp.exp(-4 * beta * c)
    hb = beta**mp.mpf("1.5") * h * mp.exp(-4 * beta * c)
    d = 2 * (1 - p - q)
    cc = 2 * c**2 - 1
    n = cc * mp.cos(2 * s) + mp.cos(alpha) * (
        cc * mp.cos(s) - 1 + mp.cos(s) ** 2
    )
    f = n - cc * d
    return {"K": kernel, "KD": kernel * d, "KF": kernel * f,
            "HDD": hb * d**2, "HDF": hb * d * f}[name]
