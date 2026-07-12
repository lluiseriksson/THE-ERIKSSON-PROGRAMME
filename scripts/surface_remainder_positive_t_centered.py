"""Mean-value centred t-box integrator for the positive K2 remainder."""

import heapq

from flint import arb

import surface_remainder_positive_physical_spatial3 as spatial
import surface_remainder_positive_physical_series_design as base
from surface_remainder_spatial_jet3 import (
    Jet3, jadd, jexp, jmul, jneg, variable_x, variable_y,
)
from surface_remainder_tjet import TJet, symmetric, tjet


PREC = base.PREC


def _calibrate(prefactors, calibration):
    qseries = [spatial.jet(value) for value in calibration]
    prefactors = dict(prefactors)
    prefactors["KF"] = spatial.sadd(
        prefactors["KF"], spatial.sneg(spatial.smul(qseries, prefactors["KD"])))
    prefactors["HDF"] = spatial.sadd(
        prefactors["HDF"], spatial.sneg(spatial.smul(qseries, prefactors["HDD"])))
    return prefactors


def _remove_constant_and_linear(phase: Jet3, gx: arb, gy: arb) -> Jet3:
    coefficients = dict(phase.coefficients)
    coefficients[0, 0] = tjet(0)
    coefficients[1, 0] = phase.get(1, 0)-gx
    coefficients[0, 1] = phase.get(0, 1)-gy
    return Jet3(coefficients)


def centered_cell(delta: arb, t_eval: arb, slo: arb, shi: arb,
                  alo: arb, ahi: arb, calibration):
    """Return one internally consistent second-order t-jet track.

    ``t_eval`` is either the exact centre point or the complete parameter
    box.  Those two tracks must be assembled nonlinearly *separately*;
    combining centre values with box derivatives before quotient assembly
    would not preserve the product rule.
    """
    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    tj = tjet(t_eval, 1, 0)
    center_pref, center_phase = spatial.physical_moment_parts(
        delta, tj, variable_x(sm), variable_y(am))
    box_pref, box_phase = spatial.physical_moment_parts(
        delta, tj, variable_x(spatial.hull(slo, shi)),
        variable_y(spatial.hull(alo, ahi)))
    center_pref = _calibrate(center_pref, calibration)
    box_pref = _calibrate(box_pref, calibration)

    def corrected(prefactors, phase):
        correction = [spatial.jet(0)]+phase[1:]
        return {name: spatial.smul(value, spatial.sexp(correction))
                for name, value in prefactors.items()}

    center = corrected(center_pref, center_phase)
    box = corrected(box_pref, box_phase)
    pc, pb = center_phase[0], box_phase[0]
    gx = arb(pc.get(1, 0).v.mid())
    gy = arb(pc.get(0, 1).v.mid())
    center_residual = jexp(_remove_constant_and_linear(pc, gx, gy))
    box_residual = jexp(_remove_constant_and_linear(pb, gx, gy))
    mx = [spatial.linear_moment(gx, 2*rx, order) for order in range(3)]
    my = [spatial.linear_moment(gy, 2*ry, order) for order in range(3)]
    mass = mx[0]*my[0]
    out = {}
    for name in center:
        coefficients = []
        for cc, bb in zip(center[name], box[name]):
            fc = jmul(cc, center_residual)
            fb = jmul(bb, box_residual)
            quadratic = tjet(0)
            for degree in range(3):
                for i in range(degree+1):
                    j = degree-i
                    quadratic += fc.get(i, j)*mx[i]*my[j]
            remainder_v = sum((arb(fb.get(i, j).v.abs_upper())
                               *rx**i*ry**j for i in range(4)
                               for j in range(4-i) if i+j == 3), arb(0))*mass
            remainder_d = sum((arb(fb.get(i, j).d.abs_upper())
                               *rx**i*ry**j for i in range(4)
                               for j in range(4-i) if i+j == 3), arb(0))*mass
            remainder_d2 = sum((arb(fb.get(i, j).d2.abs_upper())
                                *rx**i*ry**j for i in range(4)
                                for j in range(4-i) if i+j == 3), arb(0))*mass
            carrier = quadratic+symmetric(
                remainder_v, remainder_d, remainder_d2)
            coefficients.append(4*pc.get(0, 0).exp()*carrier)
        out[name] = coefficients
    return out


def _sadd(a, b):
    return [x+y for x, y in zip(a, b)]


def _sneg(a):
    return [-x for x in a]


def _smul(a, b):
    return [sum((a[k]*b[n-k] for k in range(n+1)), tjet(0))
            for n in range(PREC)]


def _sinv(a):
    out = [tjet(0) for _ in range(PREC)]
    out[0] = a[0].inv()
    for n in range(1, PREC):
        out[n] = -out[0]*sum((a[k]*out[n-k] for k in range(1, n+1)),
                             tjet(0))
    return out


def assemble_y(moments, delta: arb):
    d = [tjet(delta), tjet(1)]+[tjet(0) for _ in range(PREC-2)]
    numerator = _sadd(_smul(moments["KD"], moments["HDF"]),
                      _sneg(_smul(moments["KF"], moments["HDD"])))
    denominator_inverse = _sinv(_smul(_smul(_smul(d, d), d), d))
    kd_inverse = _sinv(moments["KD"])
    return [4*x for x in _smul(
        numerator, _smul(denominator_inverse, _smul(kd_inverse, kd_inverse)))]


def exact_head(delta: arb, t: TJet):
    d = [tjet(delta), tjet(1)]+[tjet(0) for _ in range(PREC-2)]
    c = (t/4).cos()
    leading = (4*c**2-1)/(8*c**3)
    r2 = (-8*c**4+15*c**2-4)/(32*c**6)
    r3 = (-12*c**6-485*c**4+796*c**2-224)/(1024*c**9)
    r4 = (28*c**8+41*c**6-1464*c**4+1856*c**2-500)/(1024*c**12)
    r5 = (12940*c**10+16077*c**8+173288*c**6-1300912*c**4
          +1358400*c**2-346112)/(262144*c**15)
    r6 = (8148*c**12+17095*c**10+10768*c**8+634576*c**6
          -2557408*c**4+2283296*c**2-549376)/(131072*c**18)
    out = [tjet(leading)]+[tjet(0) for _ in range(PREC-1)]
    for coefficient, power in ((r2, 1), (r3, 2), (r4, 3), (r5, 4), (r6, 5)):
        term = [tjet(1)]+[tjet(0) for _ in range(PREC-1)]
        for _ in range(power):
            term = _smul(term, d)
        out = _sadd(out, [coefficient*x for x in term])
    return out


def evaluate(series, perturbation: arb):
    out = tjet(0)
    for coefficient in reversed(series):
        out = out*perturbation+coefficient
    return out


def _priority_score(values, weights, tradius: arb):
    finite = all(value.v.is_finite() and value.d.is_finite()
                 and value.d2.is_finite()
                 for coefficients in values.values() for value in coefficients)
    if not finite:
        return float("inf")
    return sum(weights[name, order]
               *(float(value.v.rad())
                 + float(tradius*value.d.abs_upper())
                 + float(tradius**2*value.d2.abs_upper()/2))
               for name, coefficients in values.items()
               for order, value in enumerate(coefficients))


def adaptive_moments(delta: arb, t_eval: arb, tradius: arb,
                     max_cells: int = 4096, seed_grid: int = 8,
                     evaluation_ball: arb | None = None):
    pilot = base.integrate_moments(delta, t_eval, 24)
    ratio = pilot["KF"]/pilot["KD"]
    calibration = [arb(value.mid()) for value in ratio.coeffs()]
    calibration += [arb(0)]*(PREC-len(calibration))
    qseries = base.arb_series(calibration, PREC)
    calibrated = dict(pilot)
    calibrated["KF"] = pilot["KF"]-qseries*pilot["KD"]
    calibrated["HDF"] = pilot["HDF"]-qseries*pilot["HDD"]
    weights = base.terminal_weights(
        calibrated, delta, evaluation_ball=evaluation_ball)
    heap = []
    serial = 0

    def push(slo, shi, alo, ahi):
        nonlocal serial
        values = centered_cell(delta, t_eval, slo, shi, alo, ahi, calibration)
        score = _priority_score(values, weights, tradius)
        heapq.heappush(heap, (-score, serial, slo, shi, alo, ahi, values))
        serial += 1

    width = arb("1.2")/seed_grid
    for i in range(seed_grid):
        for j in range(seed_grid):
            push(width*i, width*(i+1), width*j, width*(j+1))
    while len(heap)+3 <= max_cells:
        _, _, slo, shi, alo, ahi, _ = heapq.heappop(heap)
        sm, am = (slo+shi)/2, (alo+ahi)/2
        push(slo, sm, alo, am); push(sm, shi, alo, am)
        push(slo, sm, am, ahi); push(sm, shi, am, ahi)
    totals = {name: [tjet(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    for *_, values in heap:
        for name, coefficients in values.items():
            for order, value in enumerate(coefficients):
                totals[name][order] += value
    return totals, len(heap), calibration


def residual_track(delta: arb, t_eval: arb, tradius: arb,
                   perturbation: arb, max_cells: int, seed_grid: int):
    moments, cells, calibration = adaptive_moments(
        delta, t_eval, tradius, max_cells=max_cells,
        seed_grid=seed_grid, evaluation_ball=perturbation)
    residual = _sadd(assemble_y(moments, delta),
                     _sneg(exact_head(delta, tjet(t_eval, 1, 0))))
    return evaluate(residual, perturbation), cells, calibration


def residual_box(delta: arb, t_center: arb, t_box: arb,
                 perturbation: arb, max_cells: int = 4096,
                 seed_grid: int = 8):
    """Second-order Taylor enclosure from separate centre/box tracks."""
    tradius = arb((t_box-t_center).abs_upper())
    center, center_cells, center_calibration = residual_track(
        delta, t_center, tradius, perturbation, max_cells, seed_grid)
    box, box_cells, box_calibration = residual_track(
        delta, t_box, tradius, perturbation, max_cells, seed_grid)
    value = (center.v
             + tradius*arb(center.d.abs_upper())*arb("0 +/- 1")
             + tradius**2*arb(box.d2.abs_upper())/2*arb("0 +/- 1"))
    return (value, center.d, box.d2, center_cells+box_cells,
            (center_calibration, box_calibration))
