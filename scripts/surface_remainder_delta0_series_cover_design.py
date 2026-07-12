"""Ordered t-cover design for the head-subtracted endpoint lane.

The born width 1/50 is fixed in docs/SURFACE-REMAINDER-K2-PARTITION.md.
This driver may refine the spatial grid but not the parameter partition.
It cannot emit CERTIFIED until the Bessel and outer derivative tail charges
are implemented; its terminal word is therefore DESIGN_COVER_PASS.
"""

from fractions import Fraction

from flint import arb, ctx

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


DELTA_MAX = Fraction(1, 1000)
T_STEP = Fraction(1, 50)


def aq(value: Fraction) -> arb:
    return arb(value.numerator)/arb(value.denominator)


def born_t_boxes():
    pi_upper = Fraction(
        31415926535897932384626433832795028841971693993751,
        10**49,
    )
    cursor = Fraction(0)
    while cursor < pi_upper:
        upper = min(cursor+T_STEP, pi_upper)
        yield cursor, upper
        cursor = upper


def judge_box(lo: Fraction, hi: Fraction,
              grids=(96, 192)) -> tuple[int, arb, arb, arb]:
    lane = hull(arb(0), aq(DELTA_MAX))
    t = hull(aq(lo), aq(hi))
    _, _, r3, theta3 = closed_forms(t)
    slack = theta3-arb(r3.abs_upper())
    for grid in grids:
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
            aq(DELTA_MAX), kd_lower, arb(10), companion+flat)
        margin = (slack-coefficient3*aq(DELTA_MAX)
                  -value_charge*aq(DELTA_MAX)**2)
        if margin > 0:
            return grid, coefficient3, value_charge, margin
    raise RuntimeError("unresolved endpoint series box [%s,%s]" %
                       (float(lo), float(hi)))


def cover() -> tuple[int, int]:
    boxes = list(born_t_boxes())
    refined = 0
    for lo, hi in boxes:
        grid, coefficient3, value_charge, margin = judge_box(lo, hi)
        refined += int(grid > 96)
        print("t-box [%s,%s]: grid=%d Y3_abs<=%s "
              "C_value<=%s margin>=%s" %
              (float(lo), float(hi), grid, coefficient3.str(10),
               value_charge.str(10), margin.str(10)), flush=True)
    print("DESIGN_COVER_PASS: endpoint nominal series on [0,1/1000] x "
          "[0,pi]; t_boxes=%d refined_grid_boxes=%d; Bessel and outer "
          "derivative tails remain OPEN" % (len(boxes), refined), flush=True)
    return len(boxes), refined


if __name__ == "__main__":
    ctx.prec = 140
    cover()
