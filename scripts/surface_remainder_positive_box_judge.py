"""Parameterized terminal accounting for one positive K2 parameter box."""

import argparse
from time import perf_counter

from flint import arb, ctx

import surface_remainder_companion_error_ordered as companion
import surface_remainder_positive_stress_terminal as terminal
import surface_remainder_positive_t_centered as remainder


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--delta-lo", required=True)
    parser.add_argument("--delta-hi", required=True)
    parser.add_argument("--t-lo", required=True)
    parser.add_argument("--t-hi", required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    ctx.prec = 120
    started = perf_counter()
    delta_lo, delta_hi = arb(args.delta_lo), arb(args.delta_hi)
    t_lo, t_hi = arb(args.t_lo), arb(args.t_hi)
    if not (0 < delta_lo < delta_hi <= arb("0.05")):
        raise ValueError("positive delta box outside K2 lane")
    if not (0 <= t_lo < t_hi <= arb.pi()):
        raise ValueError("t box outside physical lane")
    delta_center, delta_radius = (delta_lo+delta_hi)/2, (delta_hi-delta_lo)/2
    t_center, t_radius = (t_lo+t_hi)/2, (t_hi-t_lo)/2
    perturbation = remainder.spatial.hull(-delta_radius, delta_radius)
    delta_box = remainder.spatial.hull(delta_lo, delta_hi)
    t_box = remainder.spatial.hull(t_lo, t_hi)
    print("K2 BOX", delta_lo, delta_hi, t_lo, t_hi, flush=True)

    # Cheap auxiliary failures must occur before the centre ladder.
    delta_moments, delta_cells, delta_calibration = \
        remainder.parallel_uniform_moments(delta_box, t_box, grid=8, workers=4)
    delta_series, _ = terminal.residual_from_moments(
        delta_moments, delta_box, t_box, arb(0))
    delta_tail = arb(delta_series[6].v.abs_upper())*delta_radius**6
    original = remainder.uncalibrated_moments(
        delta_moments, delta_calibration)
    box_values = {name: series[0].v for name, series in original.items()}
    kd_lower = arb(box_values["KD"].lower())
    moment_abs = max(arb(value.abs_upper()) for value in box_values.values())
    if not kd_lower > 0:
        print("K2 BOX AUX FAIL KD", kd_lower, flush=True)
        return 1
    companion_coefficient = companion.normalized_y_error_coefficient(
        delta_hi, kd_lower, moment_abs, 6)
    companion_charge = companion_coefficient*delta_hi**6
    print("AUX delta_cells", delta_cells, "delta_tail", delta_tail,
          "KD_lower", kd_lower, "moment_abs", moment_abs,
          "companion_charge", companion_charge, flush=True)

    box_moments, box_cells, _ = remainder.parallel_uniform_moments(
        delta_center, t_box, grid=8, workers=4)
    _, box = terminal.residual_from_moments(
        box_moments, delta_center, t_box, perturbation)
    print("AUX t_box_cells", box_cells, "D4", box.d4, flush=True)

    budget = arb(150000)*delta_lo**6
    for grid in (8, 16, 24, 32):
        center_moments, center_cells, _ = remainder.parallel_uniform_moments(
            delta_center, t_center, grid=grid, workers=4)
        _, center = terminal.residual_from_moments(
            center_moments, delta_center, t_center, perturbation)
        nominal = remainder.taylor4_value_enclosure(center, box, t_radius)
        total = arb(nominal.abs_upper())+delta_tail+companion_charge
        margin = budget-total
        print("CENTER grid", grid, "cells", center_cells,
              "nominal", nominal.abs_upper(), "total", total,
              "budget", budget, "margin", margin, flush=True)
        if margin > 0:
            print("K2 BOX PASS grid", grid,
                  "elapsed_seconds", perf_counter()-started, flush=True)
            return 0
    print("K2 BOX FAIL ALL GRIDS elapsed_seconds", perf_counter()-started,
          flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
