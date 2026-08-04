"""Candidate-only low-z dispatcher for the centred K4 carrier.

This module deliberately does not replace ``surface_remainder_centered_prefactor``
in the authoritative tree.  It installs the already-regressed entire-series
branch on ``0<=z<=4`` and retains the exact endpoint recurrence above `4`.
Production/replay manifests must be regenerated under a separately named
dependency tree before any K4 or S1'''/S2''' promotion.
"""

from __future__ import annotations

from flint import arb

import surface_remainder_centered_prefactor as authoritative
from surface_bessel_entire_lowz import entire_outer_derivatives
from surface_remainder_arb_jet2 import hull


def _recurrence(z: arb, family: str) -> list[arb]:
    """Exact endpoint recurrence hull for a strictly positive z interval."""
    zl, zh = arb(z.lower()), arb(z.upper())

    def at(x: arb) -> list[arb]:
        a = (-x).exp() * x.bessel_i(1) / x
        c = (-x).exp() * x.bessel_i(0)
        if family == "A":
            return [
                a,
                -(a*x + 2*a - c) / x,
                (2*a*x**2 + 4*a*x + 6*a - 2*c*x - 3*c) / x**2,
                -(4*a*x**3 + 11*a*x**2 + 18*a*x + 24*a
                  - 4*c*x**2 - 9*c*x - 12*c) / x**3,
                (8*a*x**4 + 28*a*x**3 + 63*a*x**2 + 96*a*x + 120*a
                 - 8*c*x**3 - 24*c*x**2 - 48*c*x - 60*c) / x**4,
            ]
        if family == "B":
            b = (-x).exp() * x.bessel_i(2) / x**2
            return [
                b,
                (a*x**2 + 2*a*x + 8*a - c*x - 4*c) / x**3,
                -(2*a*x**3 + 9*a*x**2 + 16*a*x + 40*a
                  - 2*c*x**2 - 8*c*x - 20*c) / x**4,
                (4*a*x**4 + 23*a*x**3 + 72*a*x**2 + 120*a*x + 240*a
                 - 4*c*x**3 - 21*c*x**2 - 60*c*x - 120*c) / x**5,
                -(8*a*x**5 + 56*a*x**4 + 224*a*x**3 + 600*a*x**2
                  + 960*a*x + 1680*a - 8*c*x**4 - 52*c*x**3
                  - 195*c*x**2 - 480*c*x - 840*c) / x**6,
            ]
        raise ValueError(family)

    lo, hi = at(zl), at(zh)
    return [hull(hi[i], lo[i]) if i % 2 == 0
            else hull(lo[i], hi[i]) for i in range(5)]


def outer_derivatives(z: arb, family: str, terms: int = 96) -> list[arb]:
    zl, zh = arb(z.lower()), arb(z.upper())
    if zl < 0:
        raise ValueError("candidate dispatcher received a negative z ball")
    if zh <= 4:
        return entire_outer_derivatives(z, family, order=4, terms=terms)
    if zl >= 4:
        return _recurrence(z, family)
    lo = entire_outer_derivatives(hull(zl, arb(4)), family,
                                  order=4, terms=terms)
    hi = _recurrence(hull(arb(4), zh), family)
    return [hull(lo[i], hi[i]) for i in range(5)]


# ``coefficient`` and ``mirror_coefficient`` resolve this global dynamically;
# replacing only the function keeps the authoritative module byte-for-byte
# untouched while allowing an isolated candidate smoke.
authoritative.outer_derivatives = outer_derivatives
