"""Isolated extension probe for the sealed regular K2 endpoint architecture.

The authoritative ``[0,1/1000]`` dependency files remain byte-invariant.
This module merely evaluates the same proved accounting on a larger zero-based
lane.  Its output is design evidence until a new cover, manifest, and validator
are produced.
"""

from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor

from flint import arb, arb_series, ctx

import surface_remainder_delta0_series_cover_design as sealed
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_series_design import (
    endpoint_series_data, assemble_y_derivatives, nominal_moment_series,
    integrate_coefficients, PREC,
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


def wire(value):
    return value.lower().str(80), value.upper().str(80)


def unwire(value):
    return hull(arb(value[0]), arb(value[1]))


def _row_slice(arguments):
    precision, base_wire, t_wire, grid, start, stop = arguments
    ctx.prec = precision
    base, t = unwire(base_wire), unwire(t_wire)
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("kd", "kf", "hdd", "hdf")}
    width = arb(12)/grid
    for i in range(start, stop):
        for j in range(grid):
            sigma = hull(width*i, width*(i+1))
            tau = hull(width*j, width*(j+1))
            values = nominal_moment_series(base, t, sigma, tau, PREC)
            area = 4*width**2
            for name, series in values.items():
                for order, value in enumerate(series.coeffs()):
                    totals[name][order] += area*value
    return {name: [wire(value) for value in row]
            for name, row in totals.items()}


def parallel_integrate_coefficients(base, t, grid, workers=4):
    if grid % workers:
        raise ValueError("grid must divide the fixed worker count")
    step = grid//workers
    arguments = [(ctx.prec, wire(base), wire(t), grid, k*step, (k+1)*step)
                 for k in range(workers)]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        pieces = list(executor.map(_row_slice, arguments))
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("kd", "kf", "hdd", "hdf")}
    for piece in pieces:
        for name, row in piece.items():
            for order, value in enumerate(row):
                totals[name][order] += unwire(value)
    return {name: arb_series(row, PREC) for name, row in totals.items()}


def parallel_endpoint_series_data(base, t, grid, workers=4):
    series = parallel_integrate_coefficients(base, t, grid, workers)
    return series, assemble_y_derivatives(series, t)


def judge(delta_max: Fraction, lo: Fraction, hi: Fraction, grid: int,
          parallel: bool = False):
    lane, t = hull(arb(0), aq(delta_max)), hull(aq(lo), aq(hi))
    _, _, r3, theta3 = closed_forms(t)
    slack = theta3-arb(r3.abs_upper())
    moments, _ = (parallel_endpoint_series_data(lane, t, grid)
                  if parallel else endpoint_series_data(lane, t, grid=grid))
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
