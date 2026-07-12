"""Isolated extension probe for the sealed regular K2 endpoint architecture.

The authoritative ``[0,1/1000]`` dependency files remain byte-invariant.
This module merely evaluates the same proved accounting on a larger zero-based
lane.  Its output is design evidence until a new cover, manifest, and validator
are produced.
"""

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_series_cover_design as sealed
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_series_design import (
    endpoint_series_data, assemble_y_derivatives,
)
from surface_remainder_delta0_companion_error import (
    normalized_y_error_from_moment_coefficient,
    moment_error_coefficients,
)
from surface_remainder_delta0_derivative_tail import (
    add_outer_derivatives, moving_band_value_coefficients,
)
from surface_remainder_s2_direct_judge import closed_forms


def aq(value: Fraction):
    return arb(value.numerator)/arb(value.denominator)


def judge(delta_max: Fraction, lo: Fraction, hi: Fraction, grid: int):
    lane, t = hull(arb(0), aq(delta_max)), hull(aq(lo), aq(hi))
    _, _, r3, theta3 = closed_forms(t)
    slack = theta3-arb(r3.abs_upper())
    moments, _ = endpoint_series_data(lane, t, grid=grid)
    moments = add_outer_derivatives(moments)
    derivatives = assemble_y_derivatives(moments, t)
    coefficient3 = arb(derivatives.coeffs()[3].abs_upper())
    kd_lower = arb(moments["kd"].coeffs()[0].lower())
    flat = max(arb(value.upper()) for value in
               moving_band_value_coefficients().values())
    companion = max(arb(value.upper()) for value in
                    moment_error_coefficients().__dict__.values())
    value_charge = normalized_y_error_from_moment_coefficient(
        aq(delta_max), kd_lower, arb(10), companion+flat)
    margin = (slack-coefficient3*aq(delta_max)
              -value_charge*aq(delta_max)**2)
    return coefficient3, value_charge, margin


def main():
    ctx.prec = 140
    lo, hi = list(sealed.born_t_boxes())[-1]
    for delta_max in (Fraction(3, 1000), Fraction(4, 1000)):
        for grid in (96, 192):
            c3, value, margin = judge(delta_max, lo, hi, grid)
            print("EXTENSION delta", float(delta_max), "grid", grid,
                  "Y3", c3, "C_value", value, "margin", margin,
                  "PASS", bool(margin > 0), flush=True)
            if margin > 0:
                break
    print("REGULAR EXTENSION PROBE DESIGN ONLY", flush=True)


if __name__ == "__main__":
    main()
