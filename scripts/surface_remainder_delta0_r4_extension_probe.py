"""Design probe using the exact r4 head in the regular K2 lane.

The manifested ``[0,1/250]`` certificate is immutable.  This isolated judge
uses the otherwise unused fifth output coefficient of the six-term moment
series.  It subtracts the exact r4*delta^3 head and charges the fourth Taylor
coefficient, plus the existing order-four Bessel and moving-band value
errors.  No result from this module is a certificate without a fresh cover,
manifest, and validator.
"""

from fractions import Fraction

from flint import arb, arb_series, ctx

import surface_remainder_delta0_extension_probe as regular
from surface_remainder_delta0_derivative_tail import add_outer_derivatives
from surface_remainder_delta0_companion_error import (
    moment_error_coefficients,
    normalized_y_error_from_moment_coefficient,
)
from surface_remainder_delta0_derivative_tail import (
    moving_band_value_coefficients,
)
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_series_design import PREC
from surface_remainder_s2_direct_judge import closed_forms


GRID_LADDER = (192, 384, 768, 1024, 1536, 2048)
DELTA_CANDIDATE = Fraction(1, 200)  # [0,0.005], fixed before measurement


def assemble_y_through_four(moments, t):
    """Return normalized Y coefficients 0..4 from six moment terms."""
    bilinear = (moments["kd"]*moments["hdf"]
                -moments["kf"]*moments["hdd"])
    coefficients = bilinear.coeffs()+[arb(0)]*PREC
    quotient = arb_series(coefficients[1:PREC], PREC-1)
    c = (t/4).cos()
    return quotient/(2*c*moments["kd"]**2)


def judge(delta_max, lo, hi, grid, parallel=True):
    lane = regular.hull(arb(0), regular.aq(delta_max))
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    _, _, r3, theta3 = closed_forms(t)
    c = (t/4).cos()
    r4 = target_y3(c)
    if parallel:
        moments = regular.parallel_integrate_coefficients(lane, t, grid)
    else:
        rows = regular.integrate_coefficients(t, grid, base=lane)
        moments = {name: arb_series(row, PREC)
                   for name, row in rows.items()}
    moments = add_outer_derivatives(moments)
    y = assemble_y_through_four(moments, t)
    y_coefficients = y.coeffs()+[arb(0)]*5
    coefficient4 = arb(y_coefficients[4].abs_upper())
    retained_head = arb((r3+r4*lane).abs_upper())
    kd_lower = arb(moments["kd"].coeffs()[0].lower())
    flat = max(arb(value.upper()) for value in
               moving_band_value_coefficients().values())
    companion = max(arb(value.upper()) for value in
                    moment_error_coefficients().__dict__.values())
    value_charge = normalized_y_error_from_moment_coefficient(
        regular.aq(delta_max), kd_lower, arb(10), companion+flat)
    delta = regular.aq(delta_max)
    margin = theta3-retained_head-(coefficient4+value_charge)*delta**2
    return retained_head, coefficient4, value_charge, margin


def main():
    ctx.prec = 140
    lo, hi = list(regular.sealed.born_t_boxes())[-1]
    print("R4 EXTENSION DESIGN delta_max 1/200 t", lo, hi,
          "grid_ladder", GRID_LADDER, flush=True)
    for grid in GRID_LADDER:
        head, c4, value, margin = judge(
            DELTA_CANDIDATE, lo, hi, grid, parallel=True)
        print("TRY grid", grid, "head_r3_r4", head,
              "Y4", c4, "C_value", value, "margin", margin,
              "margin_lower", arb(margin.lower()), flush=True)
        if arb(margin.lower()) > 0:
            print("R4 EXTENSION ADVERSARIAL DESIGN PASS; COVER REQUIRED",
                  flush=True)
            return 0
    print("R4 EXTENSION ADVERSARIAL DESIGN FAIL", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
