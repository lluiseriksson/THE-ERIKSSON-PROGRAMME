"""Check the explicit scalar arithmetic in the far-mirror crude bound.

The analytic input is recorded in the companion document.  This executable
checks the rational geometry, polynomial monotonicity, and final
outward-rounded numerical margin.
"""

from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx


BETA0 = Fraction(1000, 9)
P0 = Fraction(101, 200)
GAP_FLOOR = Fraction(7, 20)
CONSTANT = 300_000_000_000
D1_FLOOR = Fraction(49, 100)


def aq(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def verify() -> dict[str, arb]:
    ctx.prec = 180

    # sqrt(1-p0^2)-p0 > 7/20 follows after moving p0+7/20
    # to the other side and squaring two positive rational numbers.
    left_square = 1 - P0**2
    right_square = (P0 + GAP_FLOOR) ** 2
    assert left_square > right_square

    # beta^12 exp(-(7/5) beta) decreases for beta>=beta0.
    decay_rate = 4 * GAP_FLOOR
    assert Fraction(12, 1) / BETA0 < decay_rate

    # Audit the coarse coefficient in the two-block denominator-safe
    # estimate.  The moment coefficients are
    # |a|,|b|<=160 beta^(5/2), |f|,|g|<=480 beta^(5/2),
    # u,v<=40 beta^(3/2), |w|,|x|<=120 beta^(3/2), with one
    # epsilon on every mirror moment.
    determinant_coefficient = (
        Fraction(4)
        * (Fraction(160 * 120) + Fraction(480 * 40))
        / D1_FLOOR**2
    )
    cross_coefficient = Fraction(6 * 19_200)
    denominator_change_coefficient = Fraction(160 * 480)
    assembled_coefficient = (
        Fraction(4) * cross_coefficient
        / (D1_FLOOR**2 * BETA0**5)
        + determinant_coefficient
        * denominator_change_coefficient
        / D1_FLOOR**2
    )
    assert assembled_coefficient < CONSTANT

    beta0 = aq(BETA0)
    bound = (
        arb(CONSTANT)
        * beta0**12
        * (-aq(decay_rate) * beta0).exp()
    )
    upper = arb(bound.upper())
    assert upper < arb(1) / 10**30
    assert upper < arb(19) / 20
    return {
        "bound": bound,
        "upper": upper,
        "decay_rate": aq(decay_rate),
        "assembled_coefficient": aq(assembled_coefficient),
    }


def main() -> int:
    result = verify()
    print("HIGH-BETA FAR-MIRROR SCALAR BOUND PASS")
    print("p0", P0, "gap_floor", GAP_FLOOR, "beta0", BETA0)
    print("constant", CONSTANT, "beta_power", 12)
    print(
        "derived_coefficient",
        result["assembled_coefficient"].str(50),
        "<",
        CONSTANT,
    )
    print("bound", result["bound"].str(50))
    print("upper", result["upper"].str(50), "< 1e-30 < 19/20")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
