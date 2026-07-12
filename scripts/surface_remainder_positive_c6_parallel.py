"""Parallel scalar-Arb engine for the uniform K2 sixth coefficient."""

from concurrent.futures import ProcessPoolExecutor

from flint import arb, arb_series, ctx

import surface_remainder_positive_physical_series_design as base
import surface_remainder_positive_physical_spatial3 as spatial
from surface_remainder_companion_error_ordered import moment_error_coefficients


PREC = base.PREC


def _wire(value: arb):
    return value.lower().str(80), value.upper().str(80)


def _unwire(value):
    return spatial.hull(arb(value[0]), arb(value[1]))


def _slice_worker(arguments):
    (precision, delta_wire, t_wire, grid, row_start, row_stop,
     calibration_wire) = arguments
    ctx.prec = precision
    delta, t = _unwire(delta_wire), _unwire(t_wire)
    calibration = [_unwire(value) for value in calibration_wire]
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    width = arb("1.2")/grid
    for i in range(row_start, row_stop):
        for j in range(grid):
            values = spatial.centered_cell(
                delta, t, width*i, width*(i+1),
                width*j, width*(j+1), calibration)
            for name, coefficients in values.items():
                for order, value in enumerate(coefficients):
                    totals[name][order] += value
    return {name: [_wire(value) for value in coefficients]
            for name, coefficients in totals.items()}


def uniform_moments(delta: arb, t: arb, grid: int = 8, workers: int = 4):
    if grid % workers:
        raise ValueError("grid must be divisible by worker count")
    # The q calibration is an exact algebraic gauge of the bilinear and may
    # be chosen at a point.  Dividing interval-valued pilot series adds no
    # rigor and can fail even though the subsequent box integral is finite.
    pilot = base.integrate_moments(arb(delta.mid()), arb(t.mid()), 24)
    ratio = pilot["KF"]/pilot["KD"]
    calibration = [arb(value.mid()) for value in ratio.coeffs()]
    calibration += [arb(0)]*(PREC-len(calibration))
    step = grid//workers
    arguments = [
        (ctx.prec, _wire(delta), _wire(t), grid,
         worker*step, (worker+1)*step,
         [_wire(value) for value in calibration])
        for worker in range(workers)]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        pieces = list(executor.map(_slice_worker, arguments))
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    for piece in pieces:
        for name, coefficients in piece.items():
            for order, value in enumerate(coefficients):
                totals[name][order] += _unwire(value)
    return ({name: arb_series(coefficients, PREC)
             for name, coefficients in totals.items()},
            grid*grid, calibration)


def uncalibrated_moments(moments, calibration):
    q = arb_series(calibration, PREC)
    out = dict(moments)
    out["KF"] = moments["KF"]+q*moments["KD"]
    out["HDF"] = moments["HDF"]+q*moments["HDD"]
    return out


def apply_nominal_kd_floor(moments, delta_hi: arb):
    """Intersect nominal main KD with the proved mass floor minus its error."""
    errors = moment_error_coefficients(6)
    floor = arb(1)/2-errors.kd*delta_hi**7
    coefficients = moments["KD"].coeffs()+[arb(0)]*PREC
    band = spatial.hull(floor, arb(coefficients[0].upper()))
    coefficients[0] = coefficients[0].intersection(band)
    out = dict(moments)
    out["KD"] = arb_series(coefficients, PREC)
    return out, floor


def nominal_c6(moments, delta: arb, t: arb) -> arb:
    residual = (base.assemble_y(moments, delta)
                -base.exact_head_series(delta, t))
    coefficients = residual.coeffs()
    if len(coefficients) <= 6:
        raise ValueError("sixth coefficient unavailable")
    return arb(coefficients[6].abs_upper())
