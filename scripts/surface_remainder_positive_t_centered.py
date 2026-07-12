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


def centered_cell(delta: arb, t_center: arb, t_box: arb,
                  slo: arb, shi: arb, alo: arb, ahi: arb, calibration):
    """Return moment coefficient value balls and t-derivative balls."""
    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    tc, tb = tjet(t_center, 1), tjet(t_box, 1)
    center_pref, center_phase = spatial.physical_moment_parts(
        delta, tc, variable_x(sm), variable_y(am))
    boxcenter_pref, boxcenter_phase = spatial.physical_moment_parts(
        delta, tb, variable_x(sm), variable_y(am))
    box_pref, box_phase = spatial.physical_moment_parts(
        delta, tb, variable_x(spatial.hull(slo, shi)),
        variable_y(spatial.hull(alo, ahi)))
    center_pref = _calibrate(center_pref, calibration)
    boxcenter_pref = _calibrate(boxcenter_pref, calibration)
    box_pref = _calibrate(box_pref, calibration)

    def corrected(prefactors, phase):
        correction = [spatial.jet(0)]+phase[1:]
        return {name: spatial.smul(value, spatial.sexp(correction))
                for name, value in prefactors.items()}

    center = corrected(center_pref, center_phase)
    boxcenter = corrected(boxcenter_pref, boxcenter_phase)
    box = corrected(box_pref, box_phase)
    pc, pm, pb = center_phase[0], boxcenter_phase[0], box_phase[0]
    gx = arb(pc.get(1, 0).v.mid())
    gy = arb(pc.get(0, 1).v.mid())
    center_residual = jexp(_remove_constant_and_linear(pc, gx, gy))
    boxcenter_residual = jexp(_remove_constant_and_linear(pm, gx, gy))
    box_residual = jexp(_remove_constant_and_linear(pb, gx, gy))
    mx = [spatial.linear_moment(gx, 2*rx, order) for order in range(3)]
    my = [spatial.linear_moment(gy, 2*ry, order) for order in range(3)]
    mass = mx[0]*my[0]
    out = {}
    for name in center:
        coefficients = []
        for cc, mc, bb in zip(center[name], boxcenter[name], box[name]):
            fc = jmul(cc, center_residual)
            fm = jmul(mc, boxcenter_residual)
            fb = jmul(bb, box_residual)
            quadratic_center = tjet(0)
            quadratic_box = tjet(0)
            for degree in range(3):
                for i in range(degree+1):
                    j = degree-i
                    quadratic_center += fc.get(i, j)*mx[i]*my[j]
                    quadratic_box += fm.get(i, j)*mx[i]*my[j]
            remainder_v = sum((arb(fb.get(i, j).v.abs_upper())
                               *rx**i*ry**j for i in range(4)
                               for j in range(4-i) if i+j == 3), arb(0))*mass
            remainder_d = sum((arb(fb.get(i, j).d.abs_upper())
                               *rx**i*ry**j for i in range(4)
                               for j in range(4-i) if i+j == 3), arb(0))*mass
            value = 4*pc.get(0, 0).exp().v \
                *(quadratic_center.v+remainder_v*arb("0 +/- 1"))
            derivative_carrier = quadratic_box+symmetric(remainder_v, remainder_d)
            derivative = (4*pm.get(0, 0).exp()*derivative_carrier).d
            coefficients.append(TJet(value, derivative))
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


def adaptive_moments(delta: arb, t_center: arb, t_box: arb,
                     max_cells: int = 4096, seed_grid: int = 8,
                     evaluation_ball: arb | None = None):
    pilot = base.integrate_moments(delta, t_center, 24)
    ratio = pilot["KF"]/pilot["KD"]
    calibration = [arb(value.mid()) for value in ratio.coeffs()]
    calibration += [arb(0)]*(PREC-len(calibration))
    qseries = base.arb_series(calibration, PREC)
    calibrated = dict(pilot)
    calibrated["KF"] = pilot["KF"]-qseries*pilot["KD"]
    calibrated["HDF"] = pilot["HDF"]-qseries*pilot["HDD"]
    weights = base.terminal_weights(
        calibrated, delta, evaluation_ball=evaluation_ball)
    tradius = arb((t_box-t_center).abs_upper())
    heap = []
    serial = 0

    def push(slo, shi, alo, ahi):
        nonlocal serial
        values = centered_cell(delta, t_center, t_box, slo, shi, alo, ahi,
                               calibration)
        score = sum(weights[name, order]
                    *(float(value.v.rad())+float(tradius*value.d.abs_upper()))
                    for name, coefficients in values.items()
                    for order, value in enumerate(coefficients))
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


def residual_box(delta: arb, t_center: arb, t_box: arb,
                 perturbation: arb, max_cells: int = 4096):
    moments, cells, calibration = adaptive_moments(
        delta, t_center, t_box, max_cells=max_cells,
        evaluation_ball=perturbation)
    residual = _sadd(assemble_y(moments, delta),
                     _sneg(exact_head(delta, tjet(t_center, 1))))
    centered = evaluate(residual, perturbation)
    tradius = arb((t_box-t_center).abs_upper())
    value = centered.v+tradius*arb(centered.d.abs_upper())*arb("0 +/- 1")
    return value, centered.d, cells, calibration
