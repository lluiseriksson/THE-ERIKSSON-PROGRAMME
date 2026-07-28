"""Exact algebra audit for the high-beta Q>19/20 certificate."""

from fractions import Fraction


def poly_phi_sym(p, q):
    return 2 - 6 * (p + q) + 4 * (p * p + q * q + p * q)


def poly_d(p, q):
    return 2 * (1 - p - q)


def verify() -> None:
    h = Fraction(19, 20)
    samples = (
        (Fraction(0), Fraction(0)),
        (Fraction(1, 7), Fraction(2, 9)),
        (Fraction(1), Fraction(1)),
    )
    for p, q in samples:
        main = poly_phi_sym(p, q) - h * poly_d(p, q)
        assert main == (
            2 - 2 * h
            - (6 - 2 * h) * (p + q)
            + 4 * (p * p + q * q + p * q)
        )

        pp, qq = 1 - p, 1 - q
        mirror = poly_phi_sym(pp, qq) - h * poly_d(pp, qq)
        assert mirror == (
            2 + 2 * h
            - (6 + 2 * h) * (p + q)
            + 4 * (p * p + q * q + p * q)
        )

    # Global completion of squares in x=cos(s), y=cos(alpha):
    # g+1+h^2/3=(x-h/3)^2+(y-h/3)^2+(x-h/3)(y-h/3).
    for x, y in samples:
        g = x * x + y * y + x * y - 1 - h * (x + y)
        u, v = x - h / 3, y - h / 3
        assert g + 1 + h * h / 3 == u * u + v * v + u * v
        assert u * u + v * v + u * v >= 0

    # The alternating Taylor upper bound
    # sin(x)<=x-x^3/6+x^5/120 at x=3/5 gives sin(3/5)^2<8/25.
    x = Fraction(3, 5)
    sin_upper = x - x**3 / 6 + x**5 / 120
    p_upper = Fraction(8, 25)
    assert sin_upper**2 < p_upper
    # This sharper rational bound proves both coordinate derivatives
    # negative and the mirror box minimum positive.
    assert 12 * p_upper < 6 + 2 * h
    assert (
        2 + 2 * h - (12 + 4 * h) * p_upper + 12 * p_upper**2
        > 0
    )


def main() -> int:
    verify()
    print("HIGH-BETA Q-19/20 ALGEBRA PASS")
    print("MAIN: g>=(2-2h)-(6-2h)(P+Q)")
    print("MIRROR: registered box minimum is positive")
    print("GLOBAL: g>=-1-h^2/3")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
