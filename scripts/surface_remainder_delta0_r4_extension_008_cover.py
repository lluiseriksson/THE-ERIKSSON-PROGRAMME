"""Exhaustive design cover for delta<=0.008 at physical split 1181/1000."""

import argparse
from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v5 as outer
import surface_remainder_delta0_r4_extension_008_split_probe as base
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_s2_direct_judge import closed_forms


PHYSICAL_INNER = Fraction(1181, 1000)
GRID_LADDER = (96, 192, 384)


def judge_t(lo, hi, grid):
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    core = []
    for dlo, dhi in base.CORE_BOXES:
        lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
        core.append(regular.parallel_integrate_coefficients(lane, t, grid))
    coefficient4 = arb(0)
    kd_lower = None
    moment_abs = {name: arb(0) for name in ("kd", "kf", "hdd", "hdf")}
    for dlo, dhi in base.ANNULUS_BOXES:
        source = next(core[index] for index, (_, core_hi)
                      in enumerate(base.CORE_BOXES) if dhi <= core_hi)
        moments = outer.add_outer_derivatives_box_to(
            source, dlo, dhi, PHYSICAL_INNER)
        y = assemble_y_through_four(moments, t)
        row = y.coeffs()+[arb(0)]*5
        coefficient4 = max(coefficient4, arb(row[4].abs_upper()))
        lower = arb(moments["kd"].coeffs()[0].lower())
        kd_lower = lower if kd_lower is None else min(kd_lower, lower)
        for name, value in moments.items():
            moment_abs[name] = max(
                moment_abs[name], arb(value.coeffs()[0].abs_upper()))
    lane = regular.hull(arb(0), regular.aq(base.DELTA_MAX))
    _, _, r3, theta = closed_forms(t)
    head = arb((r3+target_y3((t/4).cos())*lane).abs_upper())
    radius, bands = outer.direct_moving_band_value_coefficients_from(
        base.DELTA_MAX, PHYSICAL_INNER)
    companion = moment_error_coefficients().__dict__
    errors = {name: bands[name]+companion[name] for name in bands}
    value = outer.normalized_y_error_from_moment_coefficients(
        base.DELTA_MAX, kd_lower, moment_abs, errors)
    delta = regular.aq(base.DELTA_MAX)
    return radius, coefficient4, value, \
        theta-head-(coefficient4+value)*delta**2


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--stop-index", type=int)
    args = parser.parse_args()
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    stop = len(boxes) if args.stop_index is None else args.stop_index
    if not 0 <= args.start_index < stop <= len(boxes):
        parser.error("invalid half-open design segment")
    histogram = {grid: 0 for grid in GRID_LADDER}
    worst = None
    print("R4 008 COVER DESIGN", "boxes", len(boxes),
          "segment", args.start_index, stop,
          "core_boxes", base.CORE_BOXES,
          "annulus_boxes", base.ANNULUS_BOXES,
          "physical_inner", PHYSICAL_INNER,
          "grid_ladder", GRID_LADDER, flush=True)
    for index in range(args.start_index, stop):
        lo, hi = boxes[index]
        passed = None
        for grid in GRID_LADDER:
            try:
                radius, c4, value, margin = judge_t(lo, hi, grid)
            except (ValueError, ZeroDivisionError) as exc:
                print("TRY", index, grid, "UNRESOLVED", type(exc).__name__,
                      str(exc), flush=True)
                continue
            lower = arb(margin.lower())
            print("TRY", index, "t", lo, hi, "grid", grid,
                  "radius", radius, "Y4", c4, "C_value", value,
                  "margin_lower", lower, flush=True)
            if lower > 0:
                passed = (grid, lower)
                break
        if passed is None:
            print("R4 008 COVER DESIGN FAIL", index, flush=True)
            return 1
        histogram[passed[0]] += 1
        if worst is None or passed[1] < worst[0]:
            worst = (passed[1], index)
        print("ROW DESIGN PASS", index, "grid", passed[0],
              "margin_lower", passed[1], flush=True)
    print("R4 008 COVER DESIGN SEGMENT PASS", args.start_index, stop,
          "rows", stop-args.start_index, "histogram", histogram,
          "worst_index", worst[1], "worst_margin_lower", worst[0],
          "PRODUCTION REQUIRED", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
