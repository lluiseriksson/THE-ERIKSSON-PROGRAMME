"""Locate the coefficient-four width source at delta_max=0.006."""

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v3 as outer
import surface_remainder_delta0_r4_extension_006_probe as probe
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four


def coefficient4(moments, t):
    y = assemble_y_through_four(moments, t)
    row = y.coeffs()+[arb(0)]*5
    return arb(row[4].abs_upper()), moments["kd"].coeffs()[0]


def main():
    ctx.prec = 140
    lo, hi = list(regular.sealed.born_t_boxes())[-1]
    lane = regular.hull(arb(0), regular.aq(probe.DELTA_CANDIDATE))
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    moments = regular.parallel_integrate_coefficients(lane, t, 96)
    core_y4, core_kd = coefficient4(moments, t)
    completed = outer.add_outer_derivatives(moments, probe.DELTA_CANDIDATE)
    full_y4, full_kd = coefficient4(completed, t)
    print("R4 006 SOURCE DESIGN grid 96 core_Y4", core_y4,
          "core_KD0", core_kd, "outer_completed_Y4", full_y4,
          "outer_completed_KD0", full_kd)
    print("R4 006 SOURCE DESIGN ONLY")


if __name__ == "__main__":
    main()
