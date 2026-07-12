"""Convergent integral-form remainder for scaled I_1 and I_2.

This module implements the exact bound recorded in
docs/SURFACE-BESSEL-INTEGRAL-REMAINDER.md.  It is a reusable analytic
building block, not a standalone discharge of H_tail or H_cube.
"""

from fractions import Fraction
from math import factorial

from flint import arb, ctx


def aq(value: Fraction) -> arb:
    return arb(value.numerator)/arb(value.denominator)


def binomial_fraction(alpha: Fraction, k: int) -> Fraction:
    out = Fraction(1)
    for j in range(k):
        out *= alpha-j
    return out/Fraction(factorial(k))


def coefficient(alpha: Fraction, k: int) -> Fraction:
    return (-1)**k*binomial_fraction(alpha, k)


def upper_gamma_elementary(a: Fraction, z: arb) -> arb:
    """Elementary upper bound for Gamma(a,z), requiring z>a-1."""
    aa = aq(a)
    if not z > aa-1:
        raise ValueError("upper-gamma bound requires z>a-1")
    return (-z).exp()*z**aa/(z-aa+1)


def integral_polynomial_and_error(z: arb, p: Fraction, alpha: Fraction,
                                  order: int) -> tuple[arb, arb]:
    """Polynomial moment and rigorous unscaled-integral error."""
    if order < 0:
        raise ValueError("negative expansion order")
    poly = arb(0)
    far = upper_gamma_elementary(p+1, z)
    for k in range(order+1):
        ck = coefficient(alpha, k)
        scale = (2*z)**k
        poly += aq(ck)*aq(p+k+1).gamma()/scale
        far += aq(abs(ck))*upper_gamma_elementary(p+k+1, z)/scale
    next_c = abs(coefficient(alpha, order+1))
    local = (2*aq(next_c)*aq(p+order+2).gamma()
             /(2*z)**(order+1))
    return poly, local+far


def scaled_enclosure(z: arb, family: str, order: int = 4) -> arb:
    """Enclose exp(-z) I_1(z)/z or exp(-z) I_2(z)/z^2."""
    if family == "A":
        p = alpha = Fraction(1, 2)
        prefactor = arb(2).sqrt()/(arb.pi()*z**(arb(3)/2))
    elif family == "B":
        p = alpha = Fraction(3, 2)
        prefactor = arb(2)**(arb(3)/2)/(3*arb.pi()*z**(arb(5)/2))
    else:
        raise ValueError(family)
    poly, error = integral_polynomial_and_error(z, p, alpha, order)
    return prefactor*(poly+error*arb("0 +/- 1"))


def exact_scaled(z: arb, family: str) -> arb:
    if family == "A":
        return (-z).exp()*z.bessel_i(1)/z
    if family == "B":
        return (-z).exp()*z.bessel_i(2)/z**2
    raise ValueError(family)


def check() -> None:
    ctx.prec = 160
    for family in ("A", "B"):
        for value in (20, 40, 80, 160):
            z = arb(value)
            enclosure = scaled_enclosure(z, family, order=4)
            exact = exact_scaled(z, family)
            assert enclosure.contains(exact), (family, value, enclosure, exact)
            print(f"{family} z={value}: radius={enclosure.rad().str(8)}")
    print("integral-form scaled-Bessel remainders contain all exact samples")


if __name__ == "__main__":
    check()
