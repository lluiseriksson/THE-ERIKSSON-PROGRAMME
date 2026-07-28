"""Pure exact-rational relative Bessel companion coefficients."""

from __future__ import annotations

from fractions import Fraction
from math import factorial


def binomial_fraction(alpha: Fraction, k: int) -> Fraction:
    out = Fraction(1)
    for j in range(k):
        out *= alpha-j
    return out/Fraction(factorial(k))


def coefficient(alpha: Fraction, k: int) -> Fraction:
    return (-1)**k*binomial_fraction(alpha, k)


def family_parameters(family: str) -> tuple[Fraction, Fraction]:
    if family == "A":
        return Fraction(1, 2), Fraction(1, 2)
    if family == "B":
        return Fraction(3, 2), Fraction(3, 2)
    raise ValueError(family)


def relative_coefficients(
    family: str,
    order: int = 4,
) -> list[Fraction]:
    p, alpha = family_parameters(family)
    out = []
    rising = Fraction(1)
    for k in range(order+1):
        if k:
            rising *= p+k
        out.append(coefficient(alpha, k)*rising/Fraction(2**k))
    return out
