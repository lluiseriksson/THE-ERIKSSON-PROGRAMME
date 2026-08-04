"""Candidate-only Cauchy budget probe for the H_tail carrier.

This computes the finite-order absolute majorant already exposed by
``surface_remainder_delta0_derivative_tail`` on a complex delta circle.  It
reports the raw bilinear numerator and the exact Cauchy budget, but refuses to
call the result a certificate: the omitted coefficient tail and a joint
complex denominator floor are not supplied by the source modules.
"""

from __future__ import annotations

from flint import arb, ctx

from surface_remainder_delta0_derivative_tail import moment_majorants


RHO = arb(7) / 100
DELTA_MAX = arb(1) / 15
BETA1 = arb(1000) / 9


def theta3_at_one() -> arb:
    c = arb(1)
    t = (4 * c**2 - 1) / (8 * c**3)
    r3 = (-12 * c**6 - 485 * c**4 + 796 * c**2 - 224) / (1024 * c**9)
    return arb(r3.abs_upper()) + arb("1.10") * t / c**2 + arb("0.5") / c**3 + arb("0.05")


def cauchy_budget() -> dict[str, arb]:
    theta = theta3_at_one()
    q = DELTA_MAX / RHO
    multiplier = q**5 / (1 - q)
    # If M is a supremum for the normalized fourth-order remainder on the
    # circle, M*rho^-4*q^5/(1-q) <= beta1*Theta3 is sufficient.
    required_m = BETA1 * theta * RHO**4 / multiplier
    return {"theta3": theta, "q": q, "tail_multiplier": multiplier,
            "required_M": required_m}


def finite_order_disk_majorants() -> dict[str, arb]:
    rows = moment_majorants()
    values: dict[str, arb] = {}
    for name, terms in rows.items():
        values[name] = sum((term.c * RHO**term.p for term in terms), arb(0))
    # The sign of the bilinear numerator is irrelevant on a complex circle;
    # use the triangle inequality.  This is a raw, unnormalised quantity.
    values["raw_bilinear"] = values["kd"] * values["hdf"] + values["kf"] * values["hdd"]
    return values


def main() -> int:
    ctx.prec = 180
    budget = cauchy_budget()
    values = finite_order_disk_majorants()
    print("H_TAIL CAUCHY MAJORANT PROBE")
    for name, value in budget.items():
        print(name, value.str(30))
    for name, value in values.items():
        print(name, value.str(30))
    print("finite_order_raw_ratio",
          (values["raw_bilinear"] / budget["required_M"]).str(30))
    print("M_SUPREMUM_STATUS UNSUPPLIED")
    print("COMPLEX_DENOMINATOR_FLOOR_STATUS UNSUPPLIED")
    print("COEFFICIENT_TAIL_STATUS UNSUPPLIED")
    print("NO_H_TAIL_PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
