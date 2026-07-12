"""Design probe for the preregistered uniform sixth-coefficient shortcut."""

from flint import arb, ctx

import surface_remainder_companion_error_ordered as companion
import surface_remainder_positive_c6_parallel as coefficient
import surface_remainder_positive_physical_spatial3 as spatial


def judge(delta_lo: arb, delta_hi: arb, t_box: arb) -> bool:
    delta_box = spatial.hull(delta_lo, delta_hi)
    moments, cells, calibration = coefficient.uniform_moments(
        delta_box, t_box, grid=8, workers=4)
    nominal_c6 = coefficient.nominal_c6(moments, delta_box, t_box)
    original = coefficient.uncalibrated_moments(moments, calibration)
    box_values = {name: series.coeffs()[0] for name, series in original.items()}
    kd_lower = arb(box_values["KD"].lower())
    moment_abs = max(arb(value.abs_upper()) for value in box_values.values())
    print("UNIFORM_C6_DESIGN delta", delta_lo, delta_hi,
          "t", arb("2.9"), arb("2.92"), "cells", cells)
    print("nominal_c6", nominal_c6, "KD_lower", kd_lower,
          "moment_abs", moment_abs)
    if not kd_lower > 0:
        print("UNIFORM_C6_DESIGN FAIL KD")
        return False
    companion_c6 = companion.normalized_y_error_coefficient(
        delta_hi, kd_lower, moment_abs, 6)
    total = nominal_c6+companion_c6
    print("companion_c6", companion_c6, "total_c6", total,
          "budget_c6", arb(150000), "margin", arb(150000)-total)
    if total < arb(150000):
        print("UNIFORM_C6_DESIGN ROW PASS")
        return True
    print("UNIFORM_C6_DESIGN ROW FAIL")
    return False


def main() -> int:
    ctx.prec = 120
    t_box = spatial.hull(arb("2.9"), arb("2.92"))
    try:
        if judge(arb("0.001"), arb("0.05"), t_box):
            print("UNIFORM_C6_DESIGN FULL PASS; ONE T BOX ONLY; G2 OPEN")
            return 0
    except ValueError as error:
        print("UNIFORM_C6_DESIGN FULL REJECTED", repr(error))
    macros = (("0.001", "0.002"), ("0.002", "0.004"),
              ("0.004", "0.008"), ("0.008", "0.016"),
              ("0.016", "0.032"), ("0.032", "0.05"))
    verdicts = []
    for lo, hi in macros:
        try:
            verdicts.append(judge(arb(lo), arb(hi), t_box))
        except ValueError as error:
            print("UNIFORM_C6_DESIGN MACRO REJECTED", lo, hi, repr(error))
            verdicts.append(False)
    if all(verdicts):
        print("UNIFORM_C6_DESIGN MACRO PASS; ONE T BOX ONLY; G2 OPEN")
        return 0
    print("UNIFORM_C6_DESIGN MACRO FAIL; REVERT FAILING BIRTHS")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
