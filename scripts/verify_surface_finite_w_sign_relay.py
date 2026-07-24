"""Executable algebra audit for the finite W-sign relay.

This checks only the exact quotient identity used by the finite-beta route:
if ``F_B>0`` and the certified Wronskian ``W<0``, then ``E'<0``.  It does
not inspect a numerical cover and therefore cannot promote G2 or G6.
"""

from fractions import Fraction


def quotient_derivative(a, b, ap, bp):
    """Derivative of ``a/(2*b)`` in abstract numerator variables."""
    return (ap * b - a * bp) / (2 * b * b)


def wronskian(a, b, ap, bp):
    return 2 * (ap * b - a * bp)


def main() -> int:
    samples = (
        (Fraction(7, 5), Fraction(11, 6), Fraction(-3, 4), Fraction(5, 9)),
        (Fraction(-2, 3), Fraction(13, 7), Fraction(-5, 8), Fraction(-1, 6)),
        (Fraction(19, 11), Fraction(5, 4), Fraction(7, 10), Fraction(-9, 13)),
    )
    for a, b, ap, bp in samples:
        assert b > 0
        e_prime = quotient_derivative(a, b, ap, bp)
        w = wronskian(a, b, ap, bp)
        assert 4 * b * b * e_prime == w

        # The exponential scaling used by the finite bulk is abstracted by
        # an arbitrary positive scale s; no floating-point exp is needed.
        s = Fraction(3, 7)
        w_scaled = wronskian(s * a, s * b, s * ap, s * bp)
        assert w_scaled == s * s * w
        assert (w < 0) == (e_prime < 0)

    print("FINITE W-SIGN RELAY ALGEBRA PASS")
    print("IDENTITY 4*F_B^2*E_prime = W PASS")
    print("POSITIVE COMMON SCALING WJ = s^2*W PASS")
    print("SCOPE algebra only; finite cover and G2/G6 promotion remain open")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
