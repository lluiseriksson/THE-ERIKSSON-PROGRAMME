"""Parallel positive K2 tracks with separate KF/HDF calibrations."""

from concurrent.futures import ProcessPoolExecutor

from flint import arb, ctx

import surface_remainder_positive_physical_dual_calibration as physical
import surface_remainder_positive_physical_series_design as base
import surface_remainder_positive_physical_spatial3 as p5
import surface_remainder_positive_t_centered as algebra
from surface_remainder_tjet import TJet, tjet


PREC = base.PREC


def wire(value): return value.lower().str(80), value.upper().str(80)
def unwire(value): return p5.hull(arb(value[0]), arb(value[1]))
def wire_t(value): return tuple(wire(x) for x in value.derivatives())
def unwire_t(value): return TJet(*(unwire(x) for x in value))


def calibrations(delta, t):
    pilot = base.integrate_moments(arb(delta.mid()), arb(t.mid()), 24)
    qk, qh = pilot["KF"]/pilot["KD"], pilot["HDF"]/pilot["HDD"]
    def row(series):
        out = [arb(value.mid()) for value in series.coeffs()]
        return out+[arb(0)]*(PREC-len(out))
    return row(qk), row(qh)


def worker(arguments):
    precision, dw, tw, grid, start, stop, qkw, qhw = arguments
    ctx.prec = precision
    delta, t = unwire(dw), tjet(unwire(tw), 1, 0)
    qk, qh = [unwire(x) for x in qkw], [unwire(x) for x in qhw]
    totals = {name: [tjet(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    width = arb("1.2")/grid
    for i in range(start, stop):
        for j in range(grid):
            values = physical.centered_cell(
                delta, t, width*i, width*(i+1), width*j, width*(j+1), qk, qh)
            for name, coefficients in values.items():
                for order, value in enumerate(coefficients):
                    totals[name][order] += value
    return {name: [wire_t(value) for value in row]
            for name, row in totals.items()}


def moments(delta, t, grid=8, workers=4, qs=None):
    qk, qh = calibrations(delta, t) if qs is None else qs
    step = grid//workers
    args = [(ctx.prec, wire(delta), wire(t), grid, k*step, (k+1)*step,
             [wire(x) for x in qk], [wire(x) for x in qh])
            for k in range(workers)]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        pieces = list(executor.map(worker, args))
    totals = {name: [tjet(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    for piece in pieces:
        for name, row in piece.items():
            for order, value in enumerate(row):
                totals[name][order] += unwire_t(value)
    return totals, grid*grid, (qk, qh)


def assemble(moment_values, delta, qk, qh):
    d = [tjet(delta), tjet(1)]+[tjet(0)]*(PREC-2)
    correction = [tjet(b-a) for a, b in zip(qk, qh)]
    numerator = algebra._sadd(
        algebra._smul(moment_values["KD"], moment_values["HDF"]),
        algebra._sneg(algebra._smul(moment_values["KF"], moment_values["HDD"])))
    numerator = algebra._sadd(
        numerator, algebra._smul(correction, algebra._smul(
            moment_values["KD"], moment_values["HDD"])))
    inverse = algebra._smul(algebra._sinv(algebra._smul(
        algebra._smul(algebra._smul(d, d), d), d)),
        algebra._smul(algebra._sinv(moment_values["KD"]),
                      algebra._sinv(moment_values["KD"])))
    return [4*x for x in algebra._smul(numerator, inverse)]


def residual(moment_values, delta, t, perturbation, qs):
    series = algebra._sadd(
        assemble(moment_values, delta, *qs),
        algebra._sneg(algebra.exact_head(delta, tjet(t, 1, 0))))
    return series, algebra.evaluate_through(series, perturbation, 5)
