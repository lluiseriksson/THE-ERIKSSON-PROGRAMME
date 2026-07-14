"""Higher-head design witness for birth delta in [0.008,0.009]."""

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_positive_stress_terminal as stress
import surface_remainder_positive_t_centered as remainder


DELTA_LO = Fraction(1, 125)
DELTA_HI = Fraction(9, 1000)
DELTA_CENTER = Fraction(17, 2000)
WITNESS_INDEX = 0
GRID_LADDER = ((8, 4), (16, 4), (24, 8), (32, 8))
WORKERS = 4


def aq(value):
    return regular.aq(value)


def judge(center_grid, auxiliary_grid):
    lo, hi = list(regular.sealed.born_t_boxes())[WITNESS_INDEX]
    delta_lo, delta_hi = aq(DELTA_LO), aq(DELTA_HI)
    delta_center = aq(DELTA_CENTER)
    delta_radius = aq((DELTA_HI-DELTA_LO)/2)
    delta_box = remainder.spatial.hull(delta_lo, delta_hi)
    perturbation = remainder.spatial.hull(-delta_radius, delta_radius)
    t_lo, t_hi = aq(lo), aq(hi)
    t_center = (t_lo+t_hi)/2
    t_box = remainder.spatial.hull(t_lo, t_hi)
    t_radius = (t_hi-t_lo)/2

    center_moments, center_cells, _ = remainder.parallel_uniform_moments(
        delta_center, t_center, grid=center_grid, workers=WORKERS)
    _, center = stress.residual_from_moments(
        center_moments, delta_center, t_center, perturbation)

    box_moments, box_cells, _ = remainder.parallel_uniform_moments(
        delta_center, t_box, grid=auxiliary_grid, workers=WORKERS)
    _, box = stress.residual_from_moments(
        box_moments, delta_center, t_box, perturbation)
    nominal = remainder.taylor4_value_enclosure(center, box, t_radius)

    delta_moments, delta_cells, delta_calibration = \
        remainder.parallel_uniform_moments(
            delta_box, t_box, grid=auxiliary_grid, workers=WORKERS)
    delta_series, _ = stress.residual_from_moments(
        delta_moments, delta_box, t_box, arb(0))
    delta_tail = arb(delta_series[6].v.abs_upper())*delta_radius**6

    original = remainder.uncalibrated_moments(
        delta_moments, delta_calibration)
    box_values = {name: series[0].v for name, series in original.items()}
    kd_lower = arb(box_values["KD"].lower())
    if not kd_lower > 0:
        raise ValueError("KD leading term is not strictly positive")
    moment_abs = max(arb(value.abs_upper()) for value in box_values.values())
    companion_coefficient = stress.companion.normalized_y_error_coefficient(
        delta_hi, kd_lower, moment_abs, 6)
    companion_charge = companion_coefficient*delta_hi**6
    total = arb(nominal.abs_upper())+delta_tail+companion_charge
    budget = arb(150000)*delta_lo**6
    return {
        "center_cells": center_cells,
        "box_cells": box_cells,
        "delta_cells": delta_cells,
        "nominal": arb(nominal.abs_upper()),
        "delta_tail": delta_tail,
        "companion_charge": companion_charge,
        "kd_lower": kd_lower,
        "total": total,
        "budget": budget,
        "margin": budget-total,
    }


def main():
    ctx.prec = 120
    lo, hi = list(regular.sealed.born_t_boxes())[WITNESS_INDEX]
    print("K2 POSITIVE BIRTH008 HIGHER-HEAD WITNESS DESIGN",
          "delta", DELTA_LO, DELTA_HI, "t_index", WITNESS_INDEX,
          "t", lo, hi, "grid_ladder", GRID_LADDER,
          "workers", WORKERS, flush=True)
    for center_grid, auxiliary_grid in GRID_LADDER:
        try:
            row = judge(center_grid, auxiliary_grid)
        except (ValueError, ZeroDivisionError) as exc:
            print("TRY", center_grid, auxiliary_grid, "UNRESOLVED",
                  type(exc).__name__, str(exc), flush=True)
            continue
        print("TRY", center_grid, auxiliary_grid,
              "center_cells", row["center_cells"],
              "box_cells", row["box_cells"],
              "delta_cells", row["delta_cells"],
              "KD_lower", row["kd_lower"],
              "nominal", row["nominal"],
              "delta_tail", row["delta_tail"],
              "companion_charge", row["companion_charge"],
              "total", row["total"], "budget", row["budget"],
              "margin_lower", arb(row["margin"].lower()), flush=True)
        if arb(row["margin"].lower()) > 0:
            print("K2 POSITIVE BIRTH008 HIGHER-HEAD WITNESS DESIGN PASS",
                  "MULTI-WITNESS AND EXHAUSTIVE COVER REQUIRED", flush=True)
            return 0
    print("K2 POSITIVE BIRTH008 HIGHER-HEAD WITNESS DESIGN FAIL", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
