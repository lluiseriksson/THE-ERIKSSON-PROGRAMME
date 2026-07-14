"""Pre-registered right-endpoint witness for the moving-band deficit rate."""

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_band_gap_design as band_gap
import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v6 as outer
import surface_remainder_delta0_r4_extension_009_split_probe as base
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_s2_direct_judge import closed_forms


DELTA_MAX = Fraction(9, 1000)
PHYSICAL_INNER = Fraction(1181, 1000)
WITNESS_INDEX = 157
GRID = 384


def judge():
    lo, hi = list(regular.sealed.born_t_boxes())[WITNESS_INDEX]
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    core = []
    for dlo, dhi in base.CORE_BOXES:
        lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
        core.append(regular.parallel_integrate_coefficients(lane, t, GRID))
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
    lane = regular.hull(arb(0), regular.aq(DELTA_MAX))
    _, _, r3, theta = closed_forms(t)
    head = arb((r3+target_y3((t/4).cos())*lane).abs_upper())
    radius, bands = band_gap.direct_moving_band_value_coefficients_from(
        DELTA_MAX, PHYSICAL_INNER, regular.aq(hi))
    companion = moment_error_coefficients().__dict__
    errors = {name: bands[name]+companion[name] for name in bands}
    value = outer.normalized_y_error_from_moment_coefficients(
        DELTA_MAX, kd_lower, moment_abs, errors)
    delta = regular.aq(DELTA_MAX)
    margin = theta-head-(coefficient4+value)*delta**2
    return lo, hi, radius, coefficient4, value, margin


def main():
    ctx.prec = 140
    print("R4 009 MOVING-BAND-GAP WITNESS", "delta_max", DELTA_MAX,
          "physical_inner", PHYSICAL_INNER, "witness", WITNESS_INDEX,
          "grid", GRID, flush=True)
    try:
        lo, hi, radius, coefficient4, value, margin = judge()
    except (ValueError, ZeroDivisionError) as exc:
        print("UNRESOLVED", type(exc).__name__, str(exc), flush=True)
        print("R4 009 MOVING-BAND-GAP WITNESS FAIL", flush=True)
        return 1
    lower = arb(margin.lower())
    print("RESULT", "t", lo, hi, "radius", radius, "Y4", coefficient4,
          "C_value", value, "margin_lower", lower, flush=True)
    if lower > 0:
        print("R4 009 MOVING-BAND-GAP WITNESS PASS",
              "EXHAUSTIVE COVER REQUIRED", flush=True)
        return 0
    print("R4 009 MOVING-BAND-GAP WITNESS FAIL", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())

