"""Print the preregistered Cauchy budget for the missing H_tail majorant.

This intentionally cannot certify H_tail: it computes only the thresholds
that a future independent complex-delta supremum must meet.
"""

from flint import arb, ctx


def theta3_at_one() -> arb:
    c = arb(1)
    t = (4*c**2-1)/(8*c**3)
    r3 = (-12*c**6-485*c**4+796*c**2-224)/(1024*c**9)
    return arb(r3.abs_upper()) + arb("1.10")*t/c**2 + arb("0.5")/c**3 + arb("0.05")


def main() -> None:
    ctx.prec = 180
    rho = arb(7)/100
    delta_one = arb(1)/15
    q = delta_one/rho
    beta_one = arb(1000)/9
    budget = beta_one*theta3_at_one()
    c4_m = budget*rho**4
    tail_multiplier = q**5/(1-q)
    assert q > arb("0.9523") and q < arb("0.9524")
    assert tail_multiplier > arb("16.4540")
    assert tail_multiplier < arb("16.4541")
    assert c4_m > arb("0.0027631")
    assert c4_m < arb("0.0027632")
    print("H_TAIL CAUCHY BUDGET AUDIT")
    print("rho", rho.str(30))
    print("delta_one", delta_one.str(30))
    print("q", q.str(30))
    print("q5_over_1_minus_q", tail_multiplier.str(30))
    print("theta3_at_one", theta3_at_one().str(30))
    print("beta1_theta3", budget.str(30))
    print("required_M_for_C4", c4_m.str(30))
    print("M_SUPREMUM", "UNSUPPLIED")
    print("NO_H_TAIL_PROMOTION")


if __name__ == "__main__":
    main()
