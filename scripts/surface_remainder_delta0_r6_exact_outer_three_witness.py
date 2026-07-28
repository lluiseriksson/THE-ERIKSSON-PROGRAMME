"""R6 three-witness probe with exact core moments and split outer charge."""

from fractions import Fraction

from flint import arb, ctx

import probe_surface_remainder_r6_companion_charge as exact
import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_010_hybrid_contract as contract
import surface_remainder_delta0_r6_extension_010_cover as cover


def judge(index):
    lo, hi = list(regular.sealed.born_t_boxes())[index]
    source, t = exact.moment_series(lo, hi)
    coefficient5 = arb(0)
    kd_lower = None
    moment_abs = {name: arb(0) for name in source}
    for dlo, dhi in contract.CORE_BOXES:
        moments = cover.outer.add_outer_derivatives_box_to(
            source, dlo, dhi, cover.PHYSICAL_INNER)
        y = cover.assemble_y_six(moments, t*4)
        coefficient5 = max(coefficient5,
                           arb(y.coeffs()[5].abs_upper()))
        lower = arb(moments["kd"].coeffs()[0].lower())
        kd_lower = lower if kd_lower is None else min(kd_lower, lower)
        for name, value in moments.items():
            moment_abs[name] = max(
                moment_abs[name], arb(value.coeffs()[0].abs_upper()))
    radius, bands = cover.outer.direct_moving_band_value_coefficients_from(
        Fraction(1, 100), cover.PHYSICAL_INNER, t.upper())
    value = cover.componentwise_value_charge(
        Fraction(1, 100), kd_lower, moment_abs, bands)
    return radius, coefficient5, value, arb(7600)-coefficient5-value


def main():
    ctx.prec = 140
    passed = True
    for index, grid in contract.WITNESSES:
        radius, coeff5, value, margin = judge(index)
        lower = arb(margin.lower())
        print("TRY", index, grid, "radius", radius,
              "Y5", coeff5.str(24), "value", value.str(24),
              "margin_lower", lower.str(24), flush=True)
        passed = passed and lower > 0
    print("R6 EXACT-OUTER THREE-WITNESS-PASS" if passed
          else "R6 EXACT-OUTER THREE-WITNESS-FAIL", flush=True)
    print("DESIGN ONLY; exhaustive production/replay and S1'''/S2''' open",
          flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
