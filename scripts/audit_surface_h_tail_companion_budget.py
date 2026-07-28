"""Falsify the superseded Bessel-companion route against the H_tail budget.

This is deliberately an obstruction audit, not a certificate.  The existing
integral remainder gives a uniform value error for the four carrier moments;
the quotient perturbation then gives a sufficient bound for the induced error
in ``Y``.  After the full-moment normalization repair, both the order-four and
order-five bounds exceed the registered endpoint budget.  This proves only
that the historical sufficient route cannot discharge H_tail; it does not
imply that H_tail is false and carries no load in the terminal weak-main proof.
"""

from flint import arb, ctx

from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_companion_error_ordered import (
    moment_error_coefficients as ordered_moment_error_coefficients,
    normalized_y_error_coefficient as ordered_normalized_y_error_coefficient,
)


def theta3_at_one():
    c = arb(1)
    t = (4*c**2-1)/(8*c**3)
    r3 = (-12*c**6-485*c**4+796*c**2-224)/(1024*c**9)
    return arb(r3.abs_upper()) + arb("1.10")*t/c**2 + arb("0.5")/c**3 + arb("0.05")


def main() -> int:
    ctx.prec = 180
    theta = theta3_at_one()
    beta1 = arb(1000)/9
    budget = beta1*theta
    # The endpoint K2 enclosure has KD >= 2 and moment absolute upper <= 10
    # as fixed inputs in the existing companion-error contract.  Express the
    # induced delta^p error as an equivalent delta^4 coefficient at beta=beta1.
    delta_ref = 1/beta1
    errors = moment_error_coefficients()
    old = ordered_normalized_y_error_coefficient(
        delta_ref, arb(2), arb(10), order=4)
    new = ordered_normalized_y_error_coefficient(
        delta_ref, arb(2), arb(10), order=5)
    old_equiv = old
    new_equiv = new*delta_ref
    print("H_TAIL_COMPANION_BUDGET_AUDIT")
    print("theta3_c1", theta.str(30))
    print("budget_beta1_theta3", budget.str(30))
    for name, value in errors.__dict__.items():
        print("moment_error", name, value.str(30))
    print("delta_ref_beta1", delta_ref.str(30))
    print("order4_Y_coefficient", old.str(30))
    print("order4_equivalent_delta4_coefficient", old_equiv.str(30))
    print("order5_Y_coefficient", new.str(30))
    print("order5_equivalent_delta4_coefficient", new_equiv.str(30))
    print("order4_over_budget", (old_equiv/budget).str(30))
    print("order5_over_budget", (new_equiv/budget).str(30))
    assert old_equiv > budget
    assert new_equiv > budget
    print("ORDER5_COMPANION_ROUTE_EXCEEDS_BUDGET")
    print("SCOPE: rigorous falsifier of a superseded sufficient route; no terminal weak-main load")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
