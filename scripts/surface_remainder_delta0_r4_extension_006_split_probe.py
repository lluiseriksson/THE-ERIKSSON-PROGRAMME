"""Six-delta-box annulus derivative probe for the 0.006 regular lane."""

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v3 as outer
import surface_remainder_delta0_r4_extension_006_probe as base
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_s2_direct_judge import closed_forms


DELTA_BOXES = tuple((Fraction(j, 1000), Fraction(j+1, 1000))
                    for j in range(6))
GRID = 96
PHYSICAL_INNER = Fraction(11, 10)


def main():
    ctx.prec = 140
    lo, hi = list(regular.sealed.born_t_boxes())[-1]
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    coefficient4 = arb(0)
    kd_lower = None
    moment_abs = {name: arb(0) for name in ("kd", "kf", "hdd", "hdf")}
    for index, (dlo, dhi) in enumerate(DELTA_BOXES):
        lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
        moments = regular.parallel_integrate_coefficients(lane, t, GRID)
        moments = outer.add_outer_derivatives_box_to(
            moments, dlo, dhi, PHYSICAL_INNER)
        y = assemble_y_through_four(moments, t)
        row = y.coeffs()+[arb(0)]*5
        c4 = arb(row[4].abs_upper())
        lower = arb(moments["kd"].coeffs()[0].lower())
        coefficient4 = max(coefficient4, c4)
        kd_lower = lower if kd_lower is None else min(kd_lower, lower)
        for name, value in moments.items():
            moment_abs[name] = max(
                moment_abs[name], arb(value.coeffs()[0].abs_upper()))
        print("DELTA ROW", index, dlo, dhi, "Y4", c4,
              "KD_lower", lower, flush=True)
    lane = regular.hull(arb(0), regular.aq(base.DELTA_CANDIDATE))
    _, _, r3, theta3 = closed_forms(t)
    r4 = target_y3((t/4).cos())
    retained = arb((r3+r4*lane).abs_upper())
    radius, bands = outer.direct_moving_band_value_coefficients_from(
        base.DELTA_CANDIDATE, PHYSICAL_INNER)
    companion = moment_error_coefficients().__dict__
    errors = {name: bands[name]+companion[name] for name in bands}
    value = outer.normalized_y_error_from_moment_coefficients(
        base.DELTA_CANDIDATE, kd_lower, moment_abs, errors)
    delta = regular.aq(base.DELTA_CANDIDATE)
    margin = theta3-retained-(coefficient4+value)*delta**2
    print("R4 006 SPLIT DESIGN grid", GRID, "delta_boxes", DELTA_BOXES,
          "physical_inner", PHYSICAL_INNER, "band_radius", radius,
          "max_Y4", coefficient4,
          "C_value", value, "margin", margin,
          "margin_lower", arb(margin.lower()), flush=True)
    if arb(margin.lower()) > 0:
        print("R4 006 SPLIT ADVERSARIAL DESIGN PASS; COVER REQUIRED")
        return 0
    print("R4 006 SPLIT ADVERSARIAL DESIGN FAIL")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
