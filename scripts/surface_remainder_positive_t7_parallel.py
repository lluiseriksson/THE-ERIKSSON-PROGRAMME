"""Parallel degree-seven spatial tracks with fourth-order t jets."""

from concurrent.futures import ProcessPoolExecutor

from flint import arb, ctx

import surface_remainder_positive_physical_series_design as base
import surface_remainder_positive_physical_spatial7 as physical
import surface_remainder_positive_t_centered as algebra
from surface_remainder_tjet import TJet, tjet


PREC = base.PREC


def _wire_arb(value):
    return value.lower().str(80), value.upper().str(80)


def _unwire_arb(value):
    return physical.hull(arb(value[0]), arb(value[1]))


def _wire_tjet(value):
    return tuple(_wire_arb(item) for item in value.derivatives())


def _unwire_tjet(value):
    return TJet(*(_unwire_arb(item) for item in value))


def _worker(arguments):
    precision, dw, tw, grid, start, stop, cw = arguments
    ctx.prec = precision
    delta, t_value = _unwire_arb(dw), _unwire_arb(tw)
    t = tjet(t_value, 1, 0)
    calibration = [_unwire_arb(value) for value in cw]
    totals = {name: [tjet(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    width = arb("1.2")/grid
    for i in range(start, stop):
        for j in range(grid):
            values = physical.centered_cell(
                delta, t, width*i, width*(i+1), width*j, width*(j+1),
                calibration)
            for name, coefficients in values.items():
                for order, value in enumerate(coefficients):
                    totals[name][order] += value
    return {name: [_wire_tjet(value) for value in coefficients]
            for name, coefficients in totals.items()}


def calibration(delta, t):
    pilot = base.integrate_moments(arb(delta.mid()), arb(t.mid()), 24)
    ratio = pilot["KF"]/pilot["KD"]
    out = [arb(value.mid()) for value in ratio.coeffs()]
    return out+[arb(0)]*(PREC-len(out))


def moments(delta, t, grid=8, workers=4, q=None):
    if q is None:
        q = calibration(delta, t)
    step = grid//workers
    arguments = [(ctx.prec, _wire_arb(delta), _wire_arb(t), grid,
                  k*step, (k+1)*step, [_wire_arb(value) for value in q])
                 for k in range(workers)]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        pieces = list(executor.map(_worker, arguments))
    totals = {name: [tjet(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    for piece in pieces:
        for name, coefficients in piece.items():
            for order, value in enumerate(coefficients):
                totals[name][order] += _unwire_tjet(value)
    return totals, grid*grid, q


def residual(moment_values, delta, t, perturbation):
    series = algebra._sadd(
        algebra.assemble_y(moment_values, delta),
        algebra._sneg(algebra.exact_head(delta, tjet(t, 1, 0))))
    return series, algebra.evaluate_through(series, perturbation, 5)
