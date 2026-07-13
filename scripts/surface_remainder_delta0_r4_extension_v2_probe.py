"""Corrected exact-r4 stress probe with delta-parameterized outer bounds."""

from fractions import Fraction

from flint import arb, arb_series, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v2 as outer
from surface_remainder_delta0_companion_error import (
    moment_error_coefficients,
    normalized_y_error_from_moment_coefficient,
)
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_delta0_series_design import PREC
from surface_remainder_s2_direct_judge import closed_forms


DELTA_CANDIDATE = Fraction(1, 200)
GRID_LADDER = (96, 192, 384, 768)


def judge(delta_max, lo, hi, grid, parallel=True):
    lane = regular.hull(arb(0), regular.aq(delta_max))
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    _, _, r3, theta3 = closed_forms(t)
    r4 = target_y3((t/4).cos())
    if parallel:
        moments = regular.parallel_integrate_coefficients(lane, t, grid)
    else:
        rows = regular.integrate_coefficients(t, grid, base=lane)
        moments = {name: arb_series(row, PREC)
                   for name, row in rows.items()}
    moments = outer.add_outer_derivatives(moments, delta_max)
    y = assemble_y_through_four(moments, t)
    coefficients = y.coeffs()+[arb(0)]*5
    coefficient4 = arb(coefficients[4].abs_upper())
    retained_head = arb((r3+r4*lane).abs_upper())
    kd_lower = arb(moments["kd"].coeffs()[0].lower())
    radius, bands = outer.moving_band_value_coefficients(delta_max)
    flat = max(arb(value.upper()) for value in bands.values())
    companion = max(arb(value.upper()) for value in
                    moment_error_coefficients().__dict__.values())
    value_charge = normalized_y_error_from_moment_coefficient(
        regular.aq(delta_max), kd_lower, arb(10), companion+flat)
    delta = regular.aq(delta_max)
    margin = theta3-retained_head-(coefficient4+value_charge)*delta**2
    return radius, flat, retained_head, coefficient4, value_charge, margin


def main():
    ctx.prec = 140
    lo, hi = list(regular.sealed.born_t_boxes())[-1]
    print("R4 V2 OUTER-DOMAIN DESIGN delta_max 1/200 t", lo, hi,
          "grid_ladder", GRID_LADDER, flush=True)
    for grid in GRID_LADDER:
        try:
            radius, flat, head, c4, value, margin = judge(
                DELTA_CANDIDATE, lo, hi, grid, parallel=True)
        except (ValueError, ZeroDivisionError) as error:
            print("TRY grid", grid, "UNRESOLVED", type(error).__name__,
                  flush=True)
            continue
        lower = arb(margin.lower())
        print("TRY grid", grid, "band_radius", radius, "band_e", flat,
              "head_r3_r4", head, "Y4", c4, "C_value", value,
              "margin", margin, "margin_lower", lower, flush=True)
        if lower > 0:
            print("R4 V2 ADVERSARIAL DESIGN PASS; COVER REQUIRED", flush=True)
            return 0
    print("R4 V2 ADVERSARIAL DESIGN FAIL", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
