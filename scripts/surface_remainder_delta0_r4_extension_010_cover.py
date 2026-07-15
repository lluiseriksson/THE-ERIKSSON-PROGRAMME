"""Three-witness design judge for the tenth K2 regular birth."""

from fractions import Fraction

from flint import arb

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v7 as outer
import surface_remainder_delta0_r4_extension_010_hybrid_contract as contract
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_s2_direct_judge import closed_forms


PHYSICAL_INNER = Fraction(1181, 1000)


def judge_t(lo, hi, grid):
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    core = []
    for dlo, dhi in contract.CORE_BOXES:
        lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
        core.append(regular.parallel_integrate_coefficients(lane, t, grid))
    coefficient4 = arb(0)
    kd_lower = None
    moment_abs = {name: arb(0) for name in ("kd", "kf", "hdd", "hdf")}
    for dlo, dhi in contract.ANNULUS_BOXES:
        source = next(core[index] for index, (_, core_hi)
                      in enumerate(contract.CORE_BOXES) if dhi <= core_hi)
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
    lane = regular.hull(arb(0), regular.aq(contract.NEW_DELTA_MAX))
    _, _, r3, theta = closed_forms(t)
    head = arb((r3+target_y3((t/4).cos())*lane).abs_upper())
    radius, bands = outer.direct_moving_band_value_coefficients_from(
        contract.NEW_DELTA_MAX, PHYSICAL_INNER)
    companion = moment_error_coefficients().__dict__
    errors = {name: bands[name]+companion[name] for name in bands}
    value = outer.normalized_y_error_from_moment_coefficients(
        contract.NEW_DELTA_MAX, kd_lower, moment_abs, errors)
    delta = regular.aq(contract.NEW_DELTA_MAX)
    return radius, coefficient4, value, theta-head-(coefficient4+value)*delta**2


def main():
    from flint import ctx
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    print("R4 010 THREE-WITNESS SPLIT PROBE", "core_boxes",
          contract.CORE_BOXES, "annulus_boxes", contract.ANNULUS_BOXES,
          "witnesses", contract.WITNESSES, flush=True)
    passed = True
    for index, grid in contract.WITNESSES:
        lo, hi = boxes[index]
        try:
            radius, c4, value, margin = judge_t(lo, hi, grid)
        except (ValueError, ZeroDivisionError) as exc:
            print("TRY", index, grid, "UNRESOLVED", type(exc).__name__,
                  str(exc), flush=True)
            passed = False
            continue
        lower = arb(margin.lower())
        print("TRY", index, grid, "radius", radius, "Y4", c4,
              "C_value", value, "margin_lower", lower, flush=True)
        passed = passed and lower > 0
    print("R4 010 THREE-WITNESS-PASS" if passed
          else "R4 010 THREE-WITNESS-FAIL", flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
