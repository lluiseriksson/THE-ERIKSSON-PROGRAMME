"""Exact fixed-domain form of the Surface remainder complement.

This module is an executable identity/design contract, not an L3 or K4
certificate.  It removes artificial moving-boundary terms by returning to
fixed physical coordinates before differentiating.
"""

from __future__ import annotations

from flint import arb

from surface_remainder_arb_jet2 import Jet2, hull
from surface_remainder_carrier_jet import add, inv, lift, mul, neg, scale
from surface_remainder_centered_prefactor import (
    Dual,
    Jet,
    dual,
    jadd,
    jinv,
    jmul,
    jneg,
    jscale,
    jsquare,
    jet,
)


R_PHYSICAL = arb(6) / 5
DELTA_MAX = arb(1) / 15
R0_SQUARED = arb(16)
R1_SQUARED = arb(100)
DELTA_R2 = arb(84)


def _poly_cutoff(q: Jet2) -> Jet2:
    q2 = mul(q, q)
    q3 = mul(q2, q)
    q4 = mul(q3, q)
    q5 = mul(q4, q)
    return add(lift(1), add(scale(q3, -10), add(scale(q4, 15), scale(q5, -6))))


def cutoff_jet(delta: arb, s: arb, alpha: arb) -> Jet2:
    """Jet of chi((s^2+alpha^2)/delta) on a fixed physical box.

    Boxes that straddle a cutoff junction are deliberately rejected.  The
    integration partition must split them first; this keeps the polynomial
    identity exact instead of replacing it by an unregistered hull.
    """

    delta_jet = Jet2(delta, arb(1), arb(0))
    u = mul(lift(s**2 + alpha**2), inv(delta_jet))
    if bool(u.c0 <= R0_SQUARED):
        return lift(1)
    if bool(u.c0 >= R1_SQUARED):
        return lift(0)
    if not bool((u.c0 > R0_SQUARED) and (u.c0 < R1_SQUARED)):
        raise ValueError("cutoff box crosses R0 or R1; subdivide it")
    return _poly_cutoff(scale(add(u, lift(-R0_SQUARED)), 1 / DELTA_R2))


def _cutoff_value(q: arb) -> arb:
    return 1 - 10 * q**3 + 15 * q**4 - 6 * q**5


def cutoff_jet_enclosure(delta: arb, s: arb, alpha: arb) -> Jet2:
    """Piecewise enclosure, including cells that cross a junction.

    On a crossing cell the transition formula is evaluated only on the
    clipped q interval and then hulled with the zero derivatives of the
    adjacent constant piece. The polynomial is never extended past [0,1].
    """

    delta_jet = Jet2(delta, arb(1), arb(0))
    u = mul(lift(s**2 + alpha**2), inv(delta_jet))
    if bool(u.c0 <= R0_SQUARED):
        return lift(1)
    if bool(u.c0 >= R1_SQUARED):
        return lift(0)
    if bool((u.c0 > R0_SQUARED) and (u.c0 < R1_SQUARED)):
        return _poly_cutoff(scale(add(u, lift(-R0_SQUARED)), 1 / DELTA_R2))

    qlo = (
        arb(0)
        if u.c0.lower() <= R0_SQUARED.upper()
        else (arb(u.c0.lower()) - R0_SQUARED) / DELTA_R2
    )
    qhi = (
        arb(1)
        if u.c0.upper() >= R1_SQUARED.lower()
        else (arb(u.c0.upper()) - R0_SQUARED) / DELTA_R2
    )
    q = hull(qlo, qhi)
    chi = hull(_cutoff_value(qhi), _cutoff_value(qlo))
    chi_u = -30 * q**2 * (1 - q) ** 2 / DELTA_R2
    chi_uu = -60 * q * (1 - q) * (1 - 2 * q) / DELTA_R2**2
    first = -(u.c0 / delta) * chi_u
    second = (u.c0**2 * chi_uu + 2 * u.c0 * chi_u) / delta**2
    return Jet2(chi, hull(arb(0), first), hull(arb(0), second) / 2)


def complement_weight_jet(
    delta: arb,
    s: arb,
    alpha: arb,
    inside_physical_square: bool,
    allow_junction_hull: bool = False,
) -> Jet2:
    """Jet of 1_D-chi_delta on a cell wholly inside or outside D."""

    indicator = lift(1 if inside_physical_square else 0)
    cutoff = (
        cutoff_jet_enclosure(delta, s, alpha)
        if allow_junction_hull
        else cutoff_jet(delta, s, alpha)
    )
    return add(indicator, neg(cutoff))


def physical_complement_weight(
    delta_value: arb,
    s: Dual,
    alpha: Dual,
    inside_physical_square: bool,
) -> Jet:
    """Spatial/delta jet on a cell wholly in one cutoff piece."""

    delta = Jet(dual(delta_value), dual(1), dual(0))
    u = jmul(jadd(jsquare(jet(s)), jsquare(jet(alpha))), jinv(delta))
    if bool(u.c0.v <= R0_SQUARED):
        cutoff = jet(1)
    elif bool(u.c0.v >= R1_SQUARED):
        cutoff = jet(0)
    elif bool((u.c0.v > R0_SQUARED) and (u.c0.v < R1_SQUARED)):
        q = jscale(jadd(u, jet(-R0_SQUARED)), 1 / DELTA_R2)
        q3 = jmul(jmul(q, q), q)
        q4, q5 = jmul(q3, q), jmul(jmul(q3, q), q)
        cutoff = jadd(
            jet(1),
            jadd(jscale(q3, -10), jadd(jscale(q4, 15), jscale(q5, -6))),
        )
    else:
        raise ValueError("cutoff box crosses R0 or R1; use piecewise hull")
    return jadd(jet(1 if inside_physical_square else 0), jneg(cutoff))


def product_second_coefficient(weight: Jet2, carrier: Jet2) -> arb:
    """Return one half of the exact second delta derivative of w*f."""

    return mul(weight, carrier).c2


def fixed_outer_radius() -> arb:
    """Side length of a fixed square containing every cutoff support."""

    return arb(10) * DELTA_MAX.sqrt()


def check() -> None:
    # The fixed square contains supp chi_delta for every 0<delta<=1/15.
    qside = fixed_outer_radius()
    assert (qside**2).overlaps(R1_SQUARED * DELTA_MAX)
    assert bool(qside < arb.pi())

    # Check the exact cutoff derivative formulas at a transition point.
    delta, s, alpha = arb(1) / 15, arb("1.2"), arb("0.4")
    jet = cutoff_jet(delta, s, alpha)
    u = (s**2 + alpha**2) / delta
    q = (u - R0_SQUARED) / DELTA_R2
    chi_u = -30 * q**2 * (1 - q) ** 2 / DELTA_R2
    chi_uu = -60 * q * (1 - q) * (1 - 2 * q) / DELTA_R2**2
    expected_first = -(u / delta) * chi_u
    expected_second = (u**2 * chi_uu + 2 * u * chi_u) / delta**2
    assert jet.c1.overlaps(expected_first)
    assert (2 * jet.c2).overlaps(expected_second)

    # Algebraic product rule: c2 stores half the second derivative.
    w = Jet2(arb(2), arb(3), arb(5))
    f = Jet2(arb(7), arb(11), arb(13))
    assert product_second_coefficient(w, f) == 2 * 13 + 3 * 11 + 5 * 7
    print("Surface remainder fixed-domain complement identity K4-design OK")


if __name__ == "__main__":
    check()
