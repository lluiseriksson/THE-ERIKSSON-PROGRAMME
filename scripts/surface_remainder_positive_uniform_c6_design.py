"""Design probe for the preregistered uniform sixth-coefficient shortcut."""

from flint import arb, ctx

import surface_remainder_companion_error_ordered as companion
import surface_remainder_positive_c6_parallel as coefficient
import surface_remainder_positive_physical_spatial3 as spatial


def main() -> int:
    ctx.prec = 120
    delta_lo, delta_hi = arb("0.001"), arb("0.05")
    delta_box = spatial.hull(delta_lo, delta_hi)
    t_box = spatial.hull(arb("2.9"), arb("2.92"))
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
        return 1
    companion_c6 = companion.normalized_y_error_coefficient(
        delta_hi, kd_lower, moment_abs, 6)
    total = nominal_c6+companion_c6
    print("companion_c6", companion_c6, "total_c6", total,
          "budget_c6", arb(150000), "margin", arb(150000)-total)
    if total < arb(150000):
        print("UNIFORM_C6_DESIGN PASS; ONE T BOX ONLY; G2 OPEN")
        return 0
    print("UNIFORM_C6_DESIGN FAIL; USE FIXED MACROBOX LADDER")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
