"""Exact valuation audit for the seven scaled K4 carrier masses.

Valuations are powers of ``delta`` before differentiation.  The scaled
Bessel valuations are the powers exposed by the exact Poisson chart:
``exp(-z) I1(z)/z = delta^(3/2) * smooth`` and
``exp(-z) I2(z)/z^2 = delta^(5/2) * smooth``.  This proves only that half
powers cancel in the full masses; coefficient and tail bounds remain open.
"""

from fractions import Fraction


JACOBIAN = Fraction(1)
BETA = Fraction(-1)
A_SCALED = Fraction(3, 2)
B_SCALED = Fraction(5, 2)
KERNEL = Fraction(-5, 2)+A_SCALED
HB = Fraction(-3, 2)+B_SCALED


VALUATIONS = {
    "muF_main": JACOBIAN+BETA+KERNEL+1,
    "nuD_main": JACOBIAN+2*BETA+HB,
    "nuF_main": JACOBIAN+3*BETA+HB+1,
    "MD_mirror": JACOBIAN+KERNEL,
    "MF_mirror": JACOBIAN+KERNEL,
    "MD2r_mirror": JACOBIAN+2*BETA+HB,
    "MDFr_mirror": JACOBIAN+2*BETA+HB,
}


def main_f_first_coefficients(cc):
    """Coefficients of ``delta*sigma^2`` and ``delta*tau^2`` in main f."""
    cc = Fraction(cc)
    return -(2*cc+1), Fraction(0)


def mirror_f_constant(cc):
    return 4*Fraction(cc)


def audit():
    assert KERNEL == -1 and HB == 1
    assert set(VALUATIONS.values()) == {Fraction(0)}
    assert all(value.denominator == 1 for value in VALUATIONS.values())
    return VALUATIONS


if __name__ == "__main__":
    values = audit()
    print("K4 HALF-POWER AUDIT PASS", values,
          "COEFFICIENT AND TAIL BOUNDS STILL REQUIRED")
