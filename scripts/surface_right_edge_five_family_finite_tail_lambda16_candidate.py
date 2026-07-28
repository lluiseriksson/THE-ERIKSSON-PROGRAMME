"""Candidate finite-G5 tail budgets with the lambda endpoint 8/5.

This is deliberately a successor candidate.  The historical finite-tail
module uses exp(3/2) in its central-chart prefactor; that constant cannot be
reused for the proposed lambda extension without recalculation.
"""

from flint import arb

import surface_right_edge_five_family_finite_tail_design as base
import surface_right_edge_five_family_central_design as central
import surface_right_edge_five_family_tail_design as halfline_tail
from surface_remainder_arb_jet2 import hull


LAMBDA_MAX = arb(8) / 5


def near_bounds(delta_max=base.DELTA_MAX):
    saved = central.reduced_values
    central.reduced_values = base.low_argument_companion
    try:
        delta = hull(arb(0), delta_max)
        v = hull(base.VMIN, arb(2))
        i0, i1 = base.low_argument_companion(delta / v, v)
        gaussian = (4 * LAMBDA_MAX.exp()
                    * halfline_tail.gaussian_one_side(arb(4) / 3,
                                                       base.SIDE))
        u = {}
        for order, weight in (
                (1, 2 / arb.pi()), (3, 1 / (3 * arb.pi())),
                (5, 1 / (30 * arb.pi()))):
            u[order] = (gaussian * weight * arb(i1.abs_upper())
                        * arb(base.chain("I1", order,
                                         delta_max=delta_max).abs_upper()) / 4)
        b = {}
        for order, weight in (
                (2, 1 / arb.pi()), (4, 2 / (3 * arb.pi()))):
            b[order] = (gaussian * weight * arb(i0.abs_upper())
                        * arb(base.chain("I0", order, arb(1) / 2,
                                         delta_max=delta_max).abs_upper()))
        return u, b
    finally:
        central.reduced_values = saved


def budgets(delta_max=base.DELTA_MAX):
    nu, nb = near_bounds(delta_max)
    fu, fb = base.far_bounds(delta_max)
    return (nu[1] + fu[1], nu[3] + fu[3], nu[5] + fu[5],
            nb[2] + fb[2], nb[4] + fb[4])


if __name__ == "__main__":
    for name, value in zip(("U0", "U1", "U2", "B0", "B1"), budgets()):
        print(name, "finite_tail_lambda16_candidate", value)
