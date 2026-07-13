"""Two-delta-box derivative cover design for the regular 0.006 lane."""

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v3 as outer
import surface_remainder_delta0_r4_extension_006_probe as base
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_s2_direct_judge import closed_forms


DELTA_DERIVATIVE_BOXES = (
    (Fraction(0), Fraction(1, 200)),
    (Fraction(1, 200), Fraction(3, 500)),
)
PHYSICAL_INNER = Fraction(11, 10)
GRID_LADDER = (96, 192, 384)


def judge_t(lo, hi, grid):
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    coefficient4 = arb(0)
    kd_lower = None
    moment_abs = {name: arb(0) for name in ("kd", "kf", "hdd", "hdf")}
    for dlo, dhi in DELTA_DERIVATIVE_BOXES:
        lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
        moments = regular.parallel_integrate_coefficients(lane, t, grid)
        moments = outer.add_outer_derivatives_box_to(
            moments, dlo, dhi, PHYSICAL_INNER)
        y = assemble_y_through_four(moments, t)
        row = y.coeffs()+[arb(0)]*5
        coefficient4 = max(coefficient4, arb(row[4].abs_upper()))
        lower = arb(moments["kd"].coeffs()[0].lower())
        kd_lower = lower if kd_lower is None else min(kd_lower, lower)
        for name, value in moments.items():
            moment_abs[name] = max(
                moment_abs[name], arb(value.coeffs()[0].abs_upper()))
    lane = regular.hull(arb(0), regular.aq(base.DELTA_CANDIDATE))
    _, _, r3, theta3 = closed_forms(t)
    retained = arb((r3+target_y3((t/4).cos())*lane).abs_upper())
    radius, bands = outer.direct_moving_band_value_coefficients_from(
        base.DELTA_CANDIDATE, PHYSICAL_INNER)
    companion = moment_error_coefficients().__dict__
    errors = {name: bands[name]+companion[name] for name in bands}
    value = outer.normalized_y_error_from_moment_coefficients(
        base.DELTA_CANDIDATE, kd_lower, moment_abs, errors)
    delta = regular.aq(base.DELTA_CANDIDATE)
    margin = theta3-retained-(coefficient4+value)*delta**2
    return radius, coefficient4, value, margin


def main():
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    histogram = {grid: 0 for grid in GRID_LADDER}
    worst = None
    print("R4 006 COVER DESIGN boxes", len(boxes),
          "delta_derivative_boxes", DELTA_DERIVATIVE_BOXES,
          "physical_inner", PHYSICAL_INNER,
          "grid_ladder", GRID_LADDER, flush=True)
    for index, (lo, hi) in enumerate(boxes):
        passed = None
        for grid in GRID_LADDER:
            try:
                radius, c4, value, margin = judge_t(lo, hi, grid)
            except (ValueError, ZeroDivisionError) as error:
                print("TRY index", index, "grid", grid, "UNRESOLVED",
                      type(error).__name__, flush=True)
                continue
            lower = arb(margin.lower())
            print("TRY index", index, "t", lo, hi, "grid", grid,
                  "band_radius", radius, "Y4", c4, "C_value", value,
                  "margin", margin, "margin_lower", lower, flush=True)
            if lower > 0:
                passed = (grid, lower)
                break
        if passed is None:
            print("R4 006 COVER DESIGN FAIL index", index, flush=True)
            return 1
        histogram[passed[0]] += 1
        if worst is None or passed[1] < worst[0]:
            worst = (passed[1], index)
        print("ROW PASS index", index, "grid", passed[0],
              "margin_lower", passed[1], flush=True)
    print("R4 006 COVER DESIGN PASS rows", len(boxes),
          "histogram", histogram, "worst_index", worst[1],
          "worst_margin_lower", worst[0], "PRODUCTION REQUIRED", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
