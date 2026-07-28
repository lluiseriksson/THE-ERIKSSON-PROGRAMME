"""Positive entire-series enclosures for the low-z K4 Bessel families.

The returned list contains ordinary derivatives of
``exp(-z) I_1(z)/z`` (family ``A``) or ``exp(-z) I_2(z)/z**2`` (family
``B``), through the requested order.  This module is deliberately limited
to ``z<=4`` and is independent of the large-z integral-remainder module.
"""

from math import comb, factorial

from flint import arb


def _falling(n: int, order: int) -> int:
    out = 1
    for j in range(order):
        out *= n-j
    return out if n >= order else 0


def _base_derivatives(x: arb, family: str, order: int, terms: int) -> list[arb]:
    xmax = arb(x.abs_upper())
    if xmax > 4:
        raise ValueError("low-z entire majorant requires z<=4")
    out = [arb(0) for _ in range(order+1)]
    for k in range(terms):
        if family == "A":
            coefficient = arb(1)/(2*arb(4)**k*factorial(k)*factorial(k+1))
        elif family == "B":
            coefficient = arb(1)/(arb(4)**(k+1)*factorial(k)*factorial(k+2))
        else:
            raise ValueError(family)
        degree = 2*k
        for derivative in range(order+1):
            if degree >= derivative:
                out[derivative] += coefficient*_falling(degree, derivative)*x**(degree-derivative)

    # The coefficients and all derivative terms are nonnegative for x>=0.
    # Bound the omitted tail by a geometric majorant beginning at k=terms.
    for derivative in range(order+1):
        k = terms
        degree = 2*k
        if family == "A":
            coefficient = arb(1)/(2*arb(4)**k*factorial(k)*factorial(k+1))
            next_coefficient = arb(1)/(2*arb(4)**(k+1)*factorial(k+1)*factorial(k+2))
        else:
            coefficient = arb(1)/(arb(4)**(k+1)*factorial(k)*factorial(k+2))
            next_coefficient = arb(1)/(arb(4)**(k+2)*factorial(k+1)*factorial(k+3))
        first = (coefficient*_falling(degree, derivative)
                 *xmax**(degree-derivative) if degree >= derivative else arb(0))
        second = (next_coefficient*_falling(degree+2, derivative)
                  *xmax**(degree+2-derivative))
        ratio = second/first if first != 0 else arb(0)
        if not ratio < 1:
            raise ValueError("entire-series tail is not contractive")
        out[derivative] += first/(1-ratio)*arb("0 +/- 1")
    return out


def _point_derivatives(x: arb, family: str, order: int, terms: int) -> list[arb]:
    base = _base_derivatives(x, family, order, terms)
    result = []
    for derivative in range(order+1):
        value = arb(0)
        for k in range(derivative+1):
            value += arb(comb(derivative, k))*(-1)**(derivative-k)*base[k]
        result.append((-x).exp()*value)
    return result


def entire_outer_derivatives(z: arb, family: str, order: int = 4,
                             terms: int = 32) -> list[arb]:
    """Enclose derivatives on an Arb interval ``z<=4``."""
    if z.lower() < 0 or z.upper() > 4:
        raise ValueError("entire low-z enclosure requires 0<=z<=4")
    zl, zh = arb(z.lower()), arb(z.upper())
    lo = _point_derivatives(zl, family, order, terms)
    hi = _point_derivatives(zh, family, order, terms)
    # Complete monotonicity of exp(-z) I_n(z)/z^n gives endpoint hulls for
    # alternating derivatives.  The hull is still valid if the endpoint
    # values overlap due to outward rounding.
    return [((lo[k]+hi[k])/2 + (hi[k]-lo[k])/2*arb("0 +/- 1"))
            for k in range(order+1)]
