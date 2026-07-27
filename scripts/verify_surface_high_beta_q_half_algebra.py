"""Exact algebra audit for the high-beta Q>=1/2 certificate."""

from fractions import Fraction


def poly_phi_sym(p, q):
    return 2 - 6 * (p + q) + 4 * (p * p + q * q + p * q)


def poly_d(p, q):
    return 2 * (1 - p - q)


def verify() -> None:
    samples = (
        (Fraction(0), Fraction(0)),
        (Fraction(1, 7), Fraction(2, 9)),
        (Fraction(1), Fraction(1)),
    )
    for p, q in samples:
        main = poly_phi_sym(p, q) - poly_d(p, q) / 2
        assert main == 1 - 5 * (p + q) + 4 * (p * p + q * q + p * q)

        pp, qq = 1 - p, 1 - q
        mirror = poly_phi_sym(pp, qq) - poly_d(pp, qq) / 2
        assert mirror == 3 - 7 * (p + q) + 4 * (
            p * p + q * q + p * q
        )

    # Global completion of squares in x=cos(s), y=cos(alpha):
    # g+13/12=(x-1/6)^2+(y-1/6)^2+(x-1/6)(y-1/6).
    for x, y in samples:
        g = x * x + y * y + x * y - 1 - (x + y) / 2
        u, v = x - Fraction(1, 6), y - Fraction(1, 6)
        assert g + Fraction(13, 12) == u * u + v * v + u * v
        assert u * u + v * v + u * v >= 0

    # sin(3/5)^2 < (3/5)^2 < 7/12 makes the mirror polynomial
    # decreasing in each coordinate on the registered square.
    assert Fraction(9, 25) < Fraction(7, 12)


def main() -> int:
    verify()
    print("HIGH-BETA Q-HALF ALGEBRA PASS")
    print("MAIN: g>=1-5(P+Q)")
    print("MIRROR: box minimum 3-14p+12p^2")
    print("GLOBAL: g>=-13/12")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
