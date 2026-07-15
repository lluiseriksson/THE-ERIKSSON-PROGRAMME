"""Exact rational constant audit for the c3(beta)>0, beta>=125 proof."""

from fractions import Fraction as F
from math import factorial


def verify():
    # sqrt(2)>707/500 and cos(pi/16)>49/50 from pi<22/7 and
    # cos(x)>=1-x^2/2.
    assert F(707, 500) ** 2 < 2
    assert 1 - F(1, 2) * F(11, 56) ** 2 > F(49, 50)
    assert F(707, 500) * F(49, 50) > F(277, 200)

    # sin(pi/8)+cos(pi/8)<131/100: its square is 1+sqrt(2)/2.
    assert F(143, 100) ** 2 > 2
    assert 1 + F(143, 200) < F(131, 100) ** 2

    # Amos at x>=375/4: q>=1/(1+2/x+2/x^2)>97/100; q<1 and
    # 1/x<=4/375 give ell=q+1/x<51/50.
    amos_denominator = 1 + F(8, 375) + F(32, 140625)
    assert 1 / amos_denominator > F(97, 100)
    assert 1 + F(4, 375) < F(51, 50)

    # Uniform positivity of the regularized pointwise bracket on C.
    h_lower = (F(27, 64) * F(97, 100)
               - 4 * F(1, 125) * F(51, 50) ** 2)
    assert h_lower > F(3, 8)

    # pi<22/7 makes the exterior/inner prefactor strictly below 948.
    ratio_constant = F(22 * 128, 3) * F(625, 622) ** 2
    assert ratio_constant < 948

    # At beta=125, exp(3 beta/20)>exp(18)>18^7/7!>948 beta.
    assert F(18**7, factorial(7)) > 948 * 125
    # beta*exp(-3 beta/20) is decreasing once beta>20/3.
    assert F(1, 125) - F(3, 20) < 0
    print(
        "C3 HALFLINE CONSTANT AUDIT PASS: beta>=125, "
        "H>=3/8, exterior/inner<948*beta*exp(-3*beta/20)<1; "
        "endpoint-radius remainder still required"
    )


if __name__ == "__main__":
    verify()
