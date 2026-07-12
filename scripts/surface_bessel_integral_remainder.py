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


def family_parameters(family: str) -> tuple[Fraction, Fraction]:
    if family == "A":
        return Fraction(1, 2), Fraction(1, 2)
    if family == "B":
        return Fraction(3, 2), Fraction(3, 2)
    raise ValueError(family)


def relative_polynomial(z: arb, family: str, order: int = 4) -> arb:
    """Relative polynomial after the common 1/sqrt(2*pi) prefactor."""
    p, alpha = family_parameters(family)
    leading = aq(p+1).gamma()
    return sum((aq(coefficient(alpha, k))*aq(p+k+1).gamma()
                /(leading*(2*z)**k) for k in range(order+1)), arb(0))


def uniform_relative_constant(family: str, order: int = 4,
                              z0: int = 20) -> arb:
    """C with relative error <= C/z^(order+1) for every z>=z0.

    For every elementary far-tail summand, multiplication by z^(order+1)
    gives const*exp(-z)*z^(order+p+2)/(z-p-k).  Its logarithmic
    derivative is negative under the asserted threshold, so the far part
    is maximal at z0.  The local Taylor remainder scales exactly.
    """
    p, alpha = family_parameters(family)
    if z0 <= p+order or z0 <= order+p+2:
        raise ValueError("z0 is too small for the uniform monotonicity proof")
    z = arb(z0)
    _, error = integral_polynomial_and_error(z, p, alpha, order)
    return z**(order+1)*error/aq(p+1).gamma()


def relative_enclosure(z: arb, family: str, order: int = 4,
                       z0: int = 20) -> arb:
    """Uniform half-line relative enclosure, valid when z>=z0."""
    if not z >= z0:
        raise ValueError("relative half-line enclosure used below z0")
    constant = uniform_relative_constant(family, order, z0)
    return relative_polynomial(z, family, order) + (
        constant/z**(order+1))*arb("0 +/- 1")


def scaled_enclosure(z: arb, family: str, order: int = 4) -> arb:
    """Enclose exp(-z) I_1(z)/z or exp(-z) I_2(z)/z^2."""
    if family == "A":
        p, alpha = family_parameters(family)
        prefactor = arb(2).sqrt()/(arb.pi()*z**(arb(3)/2))
    elif family == "B":
        p, alpha = family_parameters(family)
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


def derivative_enclosures(z: arb, family: str,
                          order: int = 4) -> list[arb]:
    """Orders 0..4 obtained from exact differential recurrences.

    No derivative of the integral remainder is taken.  The recurrence
    identity exp(-z) I_0(z) = z^2 B(z)+2 A(z) closes both families using
    only the value enclosures above.
    """
    a = scaled_enclosure(z, "A", order)
    b = scaled_enclosure(z, "B", order)
    c = z**2*b+2*a
    if family == "A":
        return [
            a,
            -(a*z+2*a-c)/z,
            (2*a*z**2+4*a*z+6*a-2*c*z-3*c)/z**2,
            -(4*a*z**3+11*a*z**2+18*a*z+24*a
              -4*c*z**2-9*c*z-12*c)/z**3,
            (8*a*z**4+28*a*z**3+63*a*z**2+96*a*z+120*a
             -8*c*z**3-24*c*z**2-48*c*z-60*c)/z**4,
        ]
    if family == "B":
        return [
            b,
            (a*z**2+2*a*z+8*a-c*z-4*c)/z**3,
            -(2*a*z**3+9*a*z**2+16*a*z+40*a
              -2*c*z**2-8*c*z-20*c)/z**4,
            (4*a*z**4+23*a*z**3+72*a*z**2+120*a*z+240*a
             -4*c*z**3-21*c*z**2-60*c*z-120*c)/z**5,
            -(8*a*z**5+56*a*z**4+224*a*z**3+600*a*z**2
              +960*a*z+1680*a-8*c*z**4-52*c*z**3
              -195*c*z**2-480*c*z-840*c)/z**6,
        ]
    raise ValueError(family)


def check() -> None:
    ctx.prec = 160
    for family in ("A", "B"):
        constant = uniform_relative_constant(family, 4, 20)
        print(f"{family} uniform relative C_5={constant.str(12)}")
        for value in (20, 40, 80, 160):
            z = arb(value)
            enclosure = scaled_enclosure(z, family, order=4)
            exact = exact_scaled(z, family)
            assert enclosure.contains(exact), (family, value, enclosure, exact)
            print(f"{family} z={value}: radius={enclosure.rad().str(8)}")
            derivatives = derivative_enclosures(z, family, order=4)
            assert len(derivatives) == 5
            assert all(item.is_finite() for item in derivatives)
            relative = relative_enclosure(z, family, 4, 20)
            common = 1/(arb(2)*arb.pi()).sqrt()
            power = arb(3)/2 if family == "A" else arb(5)/2
            assert (common*z**(-power)*relative).contains(exact)
    print("integral-form scaled-Bessel remainders contain all exact samples")


if __name__ == "__main__":
    check()
