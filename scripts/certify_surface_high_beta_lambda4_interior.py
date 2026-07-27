"""Certify the denominator-safe absolute-moment splice for lambda>=4."""

from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx


BETA0 = Fraction(1000, 9)
P0 = Fraction(101, 200)
Q_BOXES = 800
MOVING_BOXES = 64
FIXED_BOXES = 512
X_SPLIT = Fraction(9, 250)  # 4/(1000/9)
X_MAX = Fraction(103, 100)
RADIUS = Fraction(6, 5)


def aq(value: Fraction | int) -> arb:
    value = Fraction(value)
    return arb(value.numerator) / value.denominator


def hull(lo: arb, hi: arb) -> arb:
    return (lo + hi) / 2 + (hi - lo) / 2 * arb("0 +/- 1")


def lower(value: arb) -> arb:
    return arb(value.lower())


def upper(value: arb) -> arb:
    return arb(value.upper())


E = (aq(RADIUS) / 2).sin() ** 2
KAPPA = E / aq(RADIUS) ** 2
SQ2PI = (2 * arb.pi()).sqrt()


def ellipticity(q: arb) -> arb:
    return 1 - E / (2 * q**2)


def main_mass_bounds(q: arb, beta: arb) -> tuple[arb, arb, arb]:
    """Return lower a, upper a, and the weighted-mass charge G."""

    ell = ellipticity(q)
    if lower(ell) <= 0:
        raise AssertionError("ellipticity is unresolved")
    z_s = 4 * beta * q
    bracket_1 = 1 - 3 / (8 * z_s) - arb("0.6") / z_s**2
    bracket_2 = (
        1 - (-beta * q * aq(RADIUS) ** 2 / 2).exp()
        - 3 / (8 * beta * q)
    )
    t1 = (
        SQ2PI / 2 / q**arb("2.5") * bracket_1 * bracket_2**2
    )

    # (1-w)^(-3/4) exp(-beta*q*w/10)<=1: its logarithmic
    # derivative is negative on the registered domain.
    derivative_upper = (
        arb(3) / (4 * (1 - E))
        - aq(Fraction(1, 10)) * aq(BETA0) * aq(P0)
    )
    assert upper(derivative_upper) < 0
    rate = arb("1.9") * ell * beta * q
    tg = (
        beta
        / (2 * SQ2PI)
        / q**arb("1.5")
        * (arb.pi() / 4)
        / (KAPPA * rate) ** 2
    )
    lower_a = t1 - tg
    if lower(lower_a) <= 0:
        raise AssertionError("principal mass lower bound is unresolved")

    upper_k = (
        (1 - E) ** arb("-0.75")
        * arb.pi()
        / (8 * SQ2PI * KAPPA * ell * q**arb("2.5"))
    )
    upper_a = 2 * upper_k
    return lower_a, upper_a, tg


def f_over_p_bound(q: arb) -> arb:
    c_value = 2 * q**2 - 1
    values = []
    for p in (arb(0), E):
        for r in (arb(0), E):
            coefficient = 4 * (
                2 * c_value * p
                + c_value * r
                - 2 * c_value
                - 2 * p * r
                + p
                + 2 * r
                - 1
            )
            values.append(arb(coefficient.abs_upper()))
    return max(values)


def radius_floor(q_floor: arb, principal: bool) -> arb:
    if principal:
        return q_floor**2 * (1 - E)
    return q_floor**2 * (1 - 2 * E) + E**2


def moment_coefficients(
    q: arb, beta: arb, radius2_floor: arb
) -> tuple[arb, arb, arb, arb]:
    mass_lower, _, weighted = main_mass_bounds(q, beta)
    a_bound = f_over_p_bound(q)
    root_floor = radius2_floor.sqrt()
    r_coefficient = (
        beta * a_bound * weighted / (4 * mass_lower)
    )
    h_coefficient = 1 / (4 * root_floor)
    w_coefficient = (
        a_bound * beta * weighted
        / (16 * root_floor * mass_lower)
    )
    x_coefficient = 4 * (
        w_coefficient + r_coefficient * h_coefficient
    )
    return (
        r_coefficient,
        h_coefficient,
        w_coefficient,
        x_coefficient,
    )


def q_range_maxima(
    lo: Fraction, hi: Fraction, principal: bool
) -> tuple[arb, arb, arb, arb]:
    maxima = [arb(0), arb(0), arb(0), arb(0)]
    q_floor = aq(lo)
    radius2 = radius_floor(q_floor, principal)
    if lower(radius2) <= 0:
        raise AssertionError("radius floor is unresolved")
    width = hi - lo
    for index in range(Q_BOXES):
        qlo = lo + width * index / Q_BOXES
        qhi = lo + width * (index + 1) / Q_BOXES
        q = hull(aq(qlo), aq(qhi))
        row = moment_coefficients(q, aq(BETA0), radius2)
        for position, value in enumerate(row):
            maxima[position] = max(maxima[position], upper(value))
    return tuple(maxima)


def rho_bound() -> tuple[arb, str]:
    worst = arb(0)
    label = ""

    def judge_x(lo: Fraction, hi: Fraction, moving: bool, index: int):
        nonlocal worst, label
        x = hull(aq(lo), aq(hi))
        p = ((arb.pi() - x) / 4).sin()
        c = ((arb.pi() - x) / 4).cos()
        if moving:
            beta_lower = aq(4 / hi)
            exponent_lower = (
                4 * arb(2).sqrt() * (1 - aq(hi) ** 2 / 96)
            )
        else:
            beta_lower = aq(BETA0)
            exponent_lower = (
                4 * beta_lower * arb(2).sqrt() * (aq(lo) / 4).sin()
            )
        _, upper_p, _ = main_mass_bounds(p, beta_lower)
        lower_c, _, _ = main_mass_bounds(c, beta_lower)
        value = (
            upper(upper_p) / lower(lower_c)
            * (-lower(exponent_lower)).exp()
        )
        value_upper = upper(value)
        if value_upper > worst:
            worst = value_upper
            label = ("moving" if moving else "fixed") + f":{index}"

    for index in range(MOVING_BOXES):
        lo = X_SPLIT * index / MOVING_BOXES
        hi = X_SPLIT * (index + 1) / MOVING_BOXES
        judge_x(lo, hi, True, index)
    width = X_MAX - X_SPLIT
    for index in range(FIXED_BOXES):
        lo = X_SPLIT + width * index / FIXED_BOXES
        hi = X_SPLIT + width * (index + 1) / FIXED_BOXES
        judge_x(lo, hi, False, index)
    return worst, label


def certify() -> dict[str, object]:
    ctx.prec = 180
    # Rational supersets for the two actual q ranges.
    p_max = Fraction(177, 250)  # 0.708 > 1/sqrt(2)
    c_min = Fraction(707, 1000)  # < 1/sqrt(2)
    c_max = Fraction(108, 125)  # 0.864 > sqrt(1-p0^2)
    assert 2 * p_max**2 > 1
    assert 2 * c_min**2 < 1
    assert c_max**2 > 1 - P0**2

    rp, hp, wp, xp = q_range_maxima(P0, p_max, True)
    rc, hc, wc, xc = q_range_maxima(c_min, c_max, False)
    rho, rho_label = rho_bound()
    if not rho < aq(Fraction(1, 100)):
        raise AssertionError(f"rho target failed: {rho}")
    adverse = (
        rho / (1 - rho) ** 2 * 4 * (rp + rc) * (hp + hc)
        + rho / (1 - rho) * xp
    )
    adverse_upper = upper(adverse)
    if not adverse_upper < aq(Fraction(3, 4)):
        raise AssertionError(f"adverse target failed: {adverse}")
    relay_margin = (
        aq(Fraction(19, 20))
        - aq(Fraction(3, 4))
        - aq(Fraction(1, 100_000))
    )
    assert lower(relay_margin) > 0
    return {
        "rp": rp,
        "hp": hp,
        "wp": wp,
        "xp": xp,
        "rc": rc,
        "hc": hc,
        "wc": wc,
        "xc": xc,
        "rho": rho,
        "rho_label": rho_label,
        "adverse": adverse_upper,
        "relay_margin": relay_margin,
    }


def main() -> int:
    result = certify()
    print("HIGH-BETA LAMBDA4 INTERIOR ABSOLUTE-MOMENT PASS")
    print(
        "CONFIG beta>=1000/9 lambda>=4 p>=101/200 "
        f"q_boxes={Q_BOXES}+{Q_BOXES} "
        f"x_boxes={MOVING_BOXES}+{FIXED_BOXES} arb_bits={ctx.prec}"
    )
    for name in ("rp", "hp", "wp", "xp", "rc", "hc", "wc", "xc"):
        print(name, result[name].str(50))
    print("rho", result["rho"].str(50), "worst", result["rho_label"])
    print("adverse_upper", result["adverse"].str(50), "< 3/4")
    print(
        "relay_margin",
        result["relay_margin"].str(50),
        "=19/20-3/4-1/100000>0",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
