"""Pre-registered physical-split probe at both endpoint t-boxes."""

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v4 as outer
import surface_remainder_delta0_r4_extension_007_probe as base
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_s2_direct_judge import closed_forms


PHYSICAL_SPLITS = (Fraction(23, 20), Fraction(119, 100))
BOX_INDICES = (0, 157)
GRID = 384


def judge(lo, hi, physical_inner):
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    core = []
    for dlo, dhi in base.CORE_BOXES:
        lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
        core.append(regular.parallel_integrate_coefficients(lane, t, GRID))
    coefficient4 = arb(0)
    kd_lower = None
    moment_abs = {name: arb(0) for name in ("kd", "kf", "hdd", "hdf")}
    for dlo, dhi in base.ANNULUS_BOXES:
        if dhi <= base.CORE_BOXES[0][1]:
            source = core[0]
        elif dhi <= base.CORE_BOXES[1][1]:
            source = core[1]
        else:
            source = core[2]
        moments = outer.add_outer_derivatives_box_to(
            source, dlo, dhi, physical_inner)
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
        base.DELTA_MAX, physical_inner)
    companion = moment_error_coefficients().__dict__
    errors = {name: bands[name]+companion[name] for name in bands}
    value = outer.normalized_y_error_from_moment_coefficients(
        base.DELTA_MAX, kd_lower, moment_abs, errors)
    delta = regular.aq(base.DELTA_MAX)
    margin = theta-head-(coefficient4+value)*delta**2
    return radius, coefficient4, value, margin


def main():
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    print("R4 007 PHYSICAL SPLIT PROBE", "splits", PHYSICAL_SPLITS,
          "box_indices", BOX_INDICES, "grid", GRID, flush=True)
    for split in PHYSICAL_SPLITS:
        passed = True
        for index in BOX_INDICES:
            lo, hi = boxes[index]
            try:
                radius, c4, value, margin = judge(lo, hi, split)
            except (ValueError, ZeroDivisionError) as exc:
                print("TRY", split, index, "UNRESOLVED", type(exc).__name__,
                      str(exc), flush=True)
                passed = False
                continue
            lower = arb(margin.lower())
            print("TRY", split, index, "radius", radius, "Y4", c4,
                  "C_value", value, "margin_lower", lower, flush=True)
            passed = passed and lower > 0
        print("SPLIT", split, "TWO-ENDPOINT-PASS" if passed else "FAIL",
              flush=True)
        if passed:
            print("R4 007 PHYSICAL SPLIT DESIGN PASS", split,
                  "EXHAUSTIVE COVER REQUIRED", flush=True)
            return 0
    print("R4 007 PHYSICAL SPLIT DESIGN FAIL", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
