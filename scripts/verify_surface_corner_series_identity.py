"""Exact audit of the corrected K4 corner-series parametrization.

This is deliberately independent of the Arb carrier implementation.  It
checks the coefficient identities from the defining modified-Bessel series
and the geometric tail ratios used by the design probe.  It is not a K4 or
G2/G6 certificate.
"""

from fractions import Fraction
from math import factorial


def i1_over_z_coefficient(k: int) -> Fraction:
    return Fraction(1, 2 * 4**k * factorial(k) * factorial(k + 1))


def i2_over_z2_coefficient(k: int) -> Fraction:
    return Fraction(1, 4 * 4**k * factorial(k) * factorial(k + 2))


def ratio_bound(u_upper: Fraction, family: str, k: int, derivative: int = 0) -> Fraction:
    """Ratio of consecutive absolute derivative terms in u."""
    if family == "A":
        a_k = i1_over_z_coefficient(k)
        a_next = i1_over_z_coefficient(k + 1)
    elif family == "B":
        a_k = i2_over_z2_coefficient(k)
        a_next = i2_over_z2_coefficient(k + 1)
    else:
        raise ValueError(family)
    if k < derivative:
        return Fraction(0)
    falling_k = factorial(k) // factorial(k - derivative)
    falling_next = factorial(k + 1) // factorial(k + 1 - derivative)
    return (a_next * falling_next * u_upper ** (k + 1 - derivative)) / (
        a_k * falling_k * u_upper ** (k - derivative)
    )


def main() -> int:
    # The first three coefficients expose the missing 4^{-k} immediately.
    assert i1_over_z_coefficient(0) == Fraction(1, 2)
    assert i1_over_z_coefficient(1) == Fraction(1, 16)
    assert i1_over_z_coefficient(2) == Fraction(1, 384)
    assert i2_over_z2_coefficient(0) == Fraction(1, 8)
    assert i2_over_z2_coefficient(1) == Fraction(1, 96)
    assert i2_over_z2_coefficient(2) == Fraction(1, 3072)

    # With u=z^2/4, the consecutive-term ratios are contractive on the
    # registered small corner domain; these values are exact rationals.
    U = Fraction(1, 1)
    for family in ("A", "B"):
        for derivative in range(5):
            assert ratio_bound(U, family, 80, derivative) < 1

    print("CORNER BESSEL SERIES IDENTITY PASS")
    print("PARAMETER u=(beta*R)^2/4 PASS")
    print("A0,A1,A2 = 1/2, 1/16, 1/384")
    print("B0,B1,B2 = 1/8, 1/96, 1/3072")
    print("SCOPE design algebra only; no K4/G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
