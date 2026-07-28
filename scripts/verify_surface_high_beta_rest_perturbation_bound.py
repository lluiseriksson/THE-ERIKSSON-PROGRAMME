"""Outward-rounded scalar bound for the third (rest) block.

This reuses exactly the Abel-layer rest-mass majorant from
``cascade1_floor_arb.py``.  The proof document records how the moment bounds
and monotonicity reduce the whole high-beta half-line to one endpoint.
"""

from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx


BETA0 = Fraction(1000, 9)
C0 = Fraction(7, 10)
V0 = Fraction(159, 500)  # 0.318
REST_TARGET = Fraction(1, 100_000)


def aq(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def rest_mass_majorant(beta: arb, c: arb) -> arb:
    """Return L=beta^(3/2)e^(-4 beta c) int_rest K.

    This is ``T5_layers`` from ``cascade1_floor_arb.py`` with the same
    inked grid, area subtraction, kernel majorant, and small-z shard.
    """

    sqrt_2pi = (2 * arb.pi()).sqrt()
    beta_c = beta * c
    z_s = 4 * beta_c
    prefactor = beta / (4 * sqrt_2pi) / c**arb("1.5")

    def rest_area(v: float) -> arb:
        branch_b = 4 * arb.pi() ** 3 * arb(v)
        if v < 0.5:
            branch_a = (
                16 * arb.pi() * arb(v) / (1 - 2 * arb(v)).sqrt()
            )
            if bool(branch_a < branch_b):
                return branch_a - arb("4.006")
        return branch_b - arb("4.006")

    def phi(v: float) -> arb:
        return (
            (1 - arb(v)) ** arb("-0.75")
            * (-2 * beta_c * arb(v)).exp()
        )

    v0 = 0.318
    step = 0.02
    cutoff = 0.9
    v = min(v0 + step, cutoff)
    layer_sum = phi(v0) * rest_area(v)
    while v < cutoff - 1e-12:
        v_next = min(v + step, cutoff)
        layer_sum += phi(v) * (rest_area(v_next) - rest_area(v))
        v = v_next

    shard = (
        (2 * arb.pi()) ** 2
        * beta**arb("2.5")
        * (-(1 - arb("0.1").sqrt()) * z_s).exp()
    )
    return prefactor * layer_sum + shard


def verify() -> dict[str, arb]:
    ctx.prec = 180

    # c=cos(t/4)>1/sqrt(2)>7/10 on 0<t<pi.
    assert Fraction(1, 2) > C0**2

    # beta^(9/2)L is decreasing.  Each layer contribution to L is
    # const(c)*beta*exp(-2 beta c v), so after multiplication its
    # polynomial power is 11/2.  The shard power is 7.
    layer_rate = 2 * C0 * V0
    assert Fraction(11, 2) / BETA0 < layer_rate
    # sqrt(1/10)<1/3, hence the shard exponential rate is > 8c/3.
    assert Fraction(1, 10) < Fraction(1, 9)
    shard_rate_floor = Fraction(8, 3) * C0
    assert Fraction(7, 1) / BETA0 < shard_rate_floor

    beta0 = aq(BETA0)
    c0 = aq(C0)
    ell = rest_mass_majorant(beta0, c0)
    ell_upper = arb(ell.upper())
    assert ell_upper < arb(1) / 10**18

    # Step 0 gives |mu_F/mu_D| <= 29.4/(beta*c)
    # +36 exp(-2 beta(c-s4)).  The moving window and
    # c-s4 >= (pi-t)/pi give beta(c-s4)>=3/(2pi).
    full_ratio = (
        arb("29.4") / (beta0 * c0)
        + 36 * (-3 / arb.pi()).exp()
    )

    # d>=1/2 and |e|<=2L imply d1=d-e>=1/2-2L.
    d1_lower = arb(1) / 2 - 2 * ell_upper
    assert d1_lower > arb("0.49")
    ratio1 = (
        full_ratio * (1 + 2 * ell_upper / d1_lower)
        + 12 * ell_upper / d1_lower
    )

    # |e|<=2L, |k|<=12L, y<=L/(2 beta), |z|<=3L/beta,
    # u1<=20 beta^(3/2), d>=1/2.  Apply the exact three-block
    # identity before taking absolute values.
    bound = (
        8
        * beta0**3
        * (
            3 * ell_upper / beta0
            + ratio1 * ell_upper / (2 * beta0)
        )
        + 16
        * beta0**3
        * (20 * beta0**arb("1.5") + ell_upper / (2 * beta0))
        * (2 * ell_upper * ratio1 + 12 * ell_upper)
    )
    upper = arb(bound.upper())
    assert upper < aq(REST_TARGET)

    return {
        "ell": ell,
        "ell_upper": ell_upper,
        "full_ratio": full_ratio,
        "d1_lower": d1_lower,
        "ratio1": ratio1,
        "bound": bound,
        "upper": upper,
    }


def main() -> int:
    result = verify()
    print("HIGH-BETA THIRD-BLOCK REST PERTURBATION PASS")
    print("beta0", BETA0, "c0", C0, "v0", V0)
    for name, value in result.items():
        print(name, value.str(50))
    print("terminal upper", result["upper"].str(50), "< 1/100000")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
