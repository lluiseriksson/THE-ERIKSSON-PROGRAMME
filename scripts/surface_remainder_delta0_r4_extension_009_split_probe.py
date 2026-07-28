"""Pre-registered exact-r4 three-witness split probe at delta=0.009."""

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v6 as outer
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_s2_direct_judge import closed_forms


DELTA_MAX = Fraction(9, 1000)
CORE_BOXES = (
    (Fraction(0), Fraction(1, 200)),
    (Fraction(1, 200), Fraction(3, 500)),
    (Fraction(3, 500), Fraction(7, 1000)),
    (Fraction(7, 1000), Fraction(1, 125)),
    (Fraction(1, 125), DELTA_MAX),
)
ANNULUS_BOXES = tuple((Fraction(j, 1000), Fraction(j+1, 1000))
                      for j in range(9))
PHYSICAL_SPLITS = (
    Fraction(1181, 1000),
    Fraction(1183, 1000),
    Fraction(237, 200),
    Fraction(1187, 1000),
)
WITNESSES = ((0, 384), (50, 192), (157, 384))


def judge(lo, hi, grid, physical_inner):
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    core = []
    for dlo, dhi in CORE_BOXES:
        lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
        core.append(regular.parallel_integrate_coefficients(lane, t, grid))
    coefficient4 = arb(0)
    kd_lower = None
    moment_abs = {name: arb(0) for name in ("kd", "kf", "hdd", "hdf")}
    for dlo, dhi in ANNULUS_BOXES:
        source = next(core[index] for index, (_, core_hi)
                      in enumerate(CORE_BOXES) if dhi <= core_hi)
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
    lane = regular.hull(arb(0), regular.aq(DELTA_MAX))
    _, _, r3, theta = closed_forms(t)
    head = arb((r3+target_y3((t/4).cos())*lane).abs_upper())
    radius, bands = outer.direct_moving_band_value_coefficients_from(
        DELTA_MAX, physical_inner)
    companion = moment_error_coefficients().__dict__
    errors = {name: bands[name]+companion[name] for name in bands}
    value = outer.normalized_y_error_from_moment_coefficients(
        DELTA_MAX, kd_lower, moment_abs, errors)
    delta = regular.aq(DELTA_MAX)
    margin = theta-head-(coefficient4+value)*delta**2
    return radius, coefficient4, value, margin


def main():
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    print("R4 009 THREE-WITNESS SPLIT PROBE", "core_boxes", CORE_BOXES,
          "annulus_boxes", ANNULUS_BOXES, "splits", PHYSICAL_SPLITS,
          "witnesses", WITNESSES, flush=True)
    for split in PHYSICAL_SPLITS:
        passed = True
        for index, grid in WITNESSES:
            lo, hi = boxes[index]
            try:
                radius, c4, value, margin = judge(lo, hi, grid, split)
            except (ValueError, ZeroDivisionError) as exc:
                print("TRY", split, index, grid, "UNRESOLVED",
                      type(exc).__name__, str(exc), flush=True)
                passed = False
                continue
            lower = arb(margin.lower())
            print("TRY", split, index, grid, "radius", radius, "Y4", c4,
                  "C_value", value, "margin_lower", lower, flush=True)
            passed = passed and lower > 0
        print("SPLIT", split,
              "THREE-WITNESS-PASS" if passed else "FAIL", flush=True)
        if passed:
            print("R4 009 SPLIT DESIGN PASS", split,
                  "EXHAUSTIVE COVER REQUIRED", flush=True)
            return 0
    print("R4 009 SPLIT DESIGN FAIL", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
