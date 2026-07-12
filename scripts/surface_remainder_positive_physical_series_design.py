"""Centered physical-coordinate delta series for positive K2 boxes.

The physical square [0,6/5]^2 is fixed.  Each normalized delta coefficient
carries a spatial value, gradient, and Hessian, so cell integration keeps
the affine cancellation and charges only a second-order spatial remainder.
The order-six Bessel companion polynomial is nominal; its value remainder
is charged separately by the direct judge.
"""

from fractions import Fraction
import heapq
from math import factorial

from flint import arb, arb_series, ctx

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_arb_jet2 import hull
from surface_remainder_centered_prefactor import (
    Dual, dadd, dcos, dexp, dinv, dmul, dneg, dsin, dsqrt, dual,
)
from surface_remainder_core_l2_arb import linear_first_moment, linear_integral


PREC = 6


def aq(value: Fraction) -> arb:
    return arb(value.numerator)/arb(value.denominator)


def sconst(value) -> list[Dual]:
    return [dual(value)]+[dual(0) for _ in range(PREC-1)]


def sadd(a, b):
    return [dadd(x, y) for x, y in zip(a, b)]


def sneg(a):
    return [dneg(x) for x in a]


def sscale(a, value):
    return [dmul(x, value) for x in a]


def smul(a, b):
    out = [dual(0) for _ in range(PREC)]
    for n in range(PREC):
        for k in range(n+1):
            out[n] = dadd(out[n], dmul(a[k], b[n-k]))
    return out


def sinv(a):
    out = [dual(0) for _ in range(PREC)]
    out[0] = dinv(a[0])
    for n in range(1, PREC):
        total = dual(0)
        for k in range(1, n+1):
            total = dadd(total, dmul(a[k], out[n-k]))
        out[n] = dneg(dmul(out[0], total))
    return out


def ssqrt(a):
    out = [dual(0) for _ in range(PREC)]
    out[0] = dsqrt(a[0])
    for n in range(1, PREC):
        total = a[n]
        for k in range(1, n):
            total = dadd(total, dneg(dmul(out[k], out[n-k])))
        out[n] = dmul(total, dinv(dmul(2, out[0])))
    return out


def sexp(a):
    out = [dual(0) for _ in range(PREC)]
    out[0] = dexp(a[0])
    for n in range(1, PREC):
        total = dual(0)
        for k in range(1, n+1):
            total = dadd(total, dmul(k, dmul(a[k], out[n-k])))
        out[n] = dmul(arb(1)/n, total)
    return out


def spoly(a, coefficients):
    out = sconst(0)
    for coefficient in reversed(coefficients):
        out = sadd(smul(out, a), sconst(aq(coefficient)))
    return out


def physical_moment_parts(delta: arb, t: arb, s: Dual, alpha: Dual):
    ds = [dual(delta), dual(1)]+[dual(0) for _ in range(PREC-2)]
    ds_inv = sinv(ds)
    c, s4 = (t/4).cos(), (t/4).sin()
    p = dmul(dsin(dmul(s, arb(1)/2)), dsin(dmul(s, arb(1)/2)))
    q = dmul(dsin(dmul(alpha, arb(1)/2)),
             dsin(dmul(alpha, arb(1)/2)))
    radius2 = dadd(
        dmul(4*c**2, dmul(dadd(1, dneg(p)), dadd(1, dneg(q)))),
        dmul(4*s4**2, dmul(p, q)))
    radius = dsqrt(radius2)
    h = sscale(ds, dinv(dmul(2, radius)))
    phase = smul(sadd(sconst(dmul(2, radius)), sconst(-4*c)), ds_inv)
    common = 1/(2*arb.pi()).sqrt()
    root3 = dmul(dmul(2, radius), dsqrt(dmul(2, radius)))
    root5 = dmul(dmul(2, radius), root3)
    kernel = smul(
        sscale(smul(ds_inv, spoly(h, relative_coefficients("A", 6))),
               2*common),
        sconst(dinv(root3)))
    hkernel = smul(
        sscale(smul(ds, spoly(h, relative_coefficients("B", 6))), common),
        sconst(dinv(root5)))
    dweight = dmul(2, dadd(1, dneg(dadd(p, q))))
    cc = 2*c**2-1
    cos_s, cos_a = dcos(s), dcos(alpha)
    n = dadd(dmul(cc, dcos(dmul(2, s))),
             dmul(cos_a, dadd(dmul(cc, cos_s),
                              dadd(-1, dmul(cos_s, cos_s)))))
    fluctuation = dadd(n, dmul(-cc, dweight))
    return {
        "KD": sscale(kernel, dweight),
        "KF": sscale(kernel, fluctuation),
        "HDD": sscale(hkernel, dmul(dweight, dweight)),
        "HDF": sscale(hkernel, dmul(dweight, fluctuation)),
    }, phase


def physical_moment_series(delta: arb, t: arb, s: Dual, alpha: Dual):
    prefactors, phase = physical_moment_parts(delta, t, s, alpha)
    exponential = sexp(phase)
    return {name: smul(value, exponential)
            for name, value in prefactors.items()}


def centered_cell(delta: arb, t: arb, slo: arb, shi: arb,
                  alo: arb, ahi: arb, calibration=None):
    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    center_prefactors, center_phase = physical_moment_parts(
        delta, t, Dual(sm, arb(1)), Dual(am, arb(0), arb(1)))
    box_prefactors, box_phase = physical_moment_parts(
        delta, t, Dual(hull(slo, shi), arb(1)),
        Dual(hull(alo, ahi), arb(0), arb(1)))
    if calibration is not None:
        qseries = [dual(value) for value in calibration]
        center_prefactors = dict(center_prefactors)
        box_prefactors = dict(box_prefactors)
        center_prefactors["KF"] = sadd(
            center_prefactors["KF"],
            sneg(smul(qseries, center_prefactors["KD"])))
        center_prefactors["HDF"] = sadd(
            center_prefactors["HDF"],
            sneg(smul(qseries, center_prefactors["HDD"])))
        box_prefactors["KF"] = sadd(
            box_prefactors["KF"],
            sneg(smul(qseries, box_prefactors["KD"])))
        box_prefactors["HDF"] = sadd(
            box_prefactors["HDF"],
            sneg(smul(qseries, box_prefactors["HDD"])))
    center_correction = [dual(0)]+center_phase[1:]
    box_correction = [dual(0)]+box_phase[1:]
    center = {name: smul(value, sexp(center_correction))
              for name, value in center_prefactors.items()}
    box = {name: smul(value, sexp(box_correction))
           for name, value in box_prefactors.items()}
    pc, pb = center_phase[0], box_phase[0]
    gx, gy = arb(pc.x.mid()), arb(pc.y.mid())
    phase_radius = (
        arb((pc.x-gx).abs_upper())*rx
        +arb((pc.y-gy).abs_upper())*ry
        +arb(pb.xx.abs_upper())*rx**2/2
        +arb(pb.xy.abs_upper())*rx*ry
        +arb(pb.yy.abs_upper())*ry**2/2)
    l0x = linear_integral(gx, 2*rx)
    l0y = linear_integral(gy, 2*ry)
    l1x = linear_first_moment(gx, 2*rx)
    l1y = linear_first_moment(gy, 2*ry)
    spatial = l0x*l0y
    phase_exp = phase_radius.exp()
    phase_error = phase_exp-1
    out = {}
    for name in center:
        coefficients = []
        for cc, bb in zip(center[name], box[name]):
            affine = cc.v*spatial+cc.x*l1x*l0y+cc.y*l0x*l1y
            hessian = (arb(bb.xx.abs_upper())*rx**2/2
                       +arb(bb.xy.abs_upper())*rx*ry
                       +arb(bb.yy.abs_upper())*ry**2/2)
            affine_abs = (arb(cc.v.abs_upper())
                          +arb(cc.x.abs_upper())*rx
                          +arb(cc.y.abs_upper())*ry)
            error = (hessian*phase_exp+affine_abs*phase_error)*spatial
            coefficients.append(
                4*pc.v.exp()*(affine+error*arb("0 +/- 1")))
        out[name] = coefficients
    return out


def integrate_moments(delta: arb, t: arb, grid: int):
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    width = arb("1.2")/grid
    for i in range(grid):
        for j in range(grid):
            values = centered_cell(delta, t, width*i, width*(i+1),
                                   width*j, width*(j+1))
            for name, coefficients in values.items():
                for order, value in enumerate(coefficients):
                    totals[name][order] += value
    return {name: arb_series(values, PREC)
            for name, values in totals.items()}


def normalized_y_series(delta: arb, t: arb, grid: int):
    moments = integrate_moments(delta, t, grid)
    ds = arb_series([delta, arb(1)], PREC)
    numerator = (moments["KD"]*moments["HDF"]
                 -moments["KF"]*moments["HDD"])
    return 4*numerator/(ds**4*moments["KD"]**2), moments


def assemble_y(moments, delta: arb):
    ds = arb_series([delta, arb(1)], PREC)
    numerator = (moments["KD"]*moments["HDF"]
                 -moments["KF"]*moments["HDD"])
    return 4*numerator/(ds**4*moments["KD"]**2)


def exact_head_series(delta: arb, t: arb):
    """Taylor series of the registered head through ``r6 delta^5``."""
    d = arb_series([delta, arb(1)], PREC)
    c = (t/4).cos()
    leading = (4*c**2-1)/(8*c**3)
    r2 = (-8*c**4+15*c**2-4)/(32*c**6)
    r3 = (-12*c**6-485*c**4+796*c**2-224)/(1024*c**9)
    r4 = (28*c**8+41*c**6-1464*c**4+1856*c**2-500) \
        /(1024*c**12)
    r5 = (12940*c**10+16077*c**8+173288*c**6-1300912*c**4
          +1358400*c**2-346112)/(262144*c**15)
    r6 = (8148*c**12+17095*c**10+10768*c**8+634576*c**6
          -2557408*c**4+2283296*c**2-549376)/(131072*c**18)
    return leading+r2*d+r3*d**2+r4*d**3+r5*d**4+r6*d**5


def evaluate_series(series: arb_series, perturbation: arb) -> arb:
    """Evaluate retained coefficients by interval Horner arithmetic."""
    out = arb(0)
    for coefficient in reversed(series.coeffs()):
        out = out*perturbation+coefficient
    return out


def head_subtracted_y_value(moments, delta: arb, t: arb,
                            perturbation: arb) -> arb:
    residual = assemble_y(moments, delta)-exact_head_series(delta, t)
    return evaluate_series(residual, perturbation)


def terminal_weights(pilot, delta: arb, target_order: int = 3,
                     evaluation_ball: arb | None = None):
    """Finite-difference Jacobian weights for one normalized-Y coefficient.

    ``target_order=3`` preserves the original derivative-remainder pilot.
    The positive-box judge instead uses ``target_order=0``: after the exact
    heads have been subtracted, its terminal quantity is the value enclosure
    on the whole delta box, not a separately majorized derivative.
    If ``evaluation_ball`` is supplied, the target is the retained Y series
    evaluated on that centred perturbation ball; this keeps every coefficient
    in the refinement sensitivity instead of optimizing one coefficient.
    """
    if not 0 <= target_order < PREC:
        raise ValueError("target order outside retained delta series")
    point = {name: arb_series([arb(value.mid()) for value in series.coeffs()],
                              PREC)
             for name, series in pilot.items()}
    weights = {}
    for name in point:
        for order in range(PREC):
            coefficient = point[name].coeffs()[order]
            step = max(abs(float(coefficient)), 1e-20)*1e-6
            plus_values = point[name].coeffs()+[arb(0)]*PREC
            minus_values = list(plus_values)
            plus_values[order] += arb(str(step))
            minus_values[order] -= arb(str(step))
            plus, minus = dict(point), dict(point)
            plus[name] = arb_series(plus_values, PREC)
            minus[name] = arb_series(minus_values, PREC)
            plus_y, minus_y = assemble_y(plus, delta), assemble_y(minus, delta)
            if evaluation_ball is None:
                change = (plus_y.coeffs()[target_order]
                          -minus_y.coeffs()[target_order])
            else:
                change = (evaluate_series(plus_y, evaluation_ball)
                          -evaluate_series(minus_y, evaluation_ball))
            derivative = change/arb(str(2*step))
            weights[name, order] = abs(float(derivative))
    return weights


def adaptive_moments(delta: arb, t: arb, max_cells: int = 4096,
                     seed_grid: int = 8, pilot_grid: int = 24,
                     target_order: int = 3,
                     evaluation_ball: arb | None = None):
    pilot = integrate_moments(delta, t, pilot_grid)
    ratio = pilot["KF"]/pilot["KD"]
    calibration = [arb(value.mid()) for value in ratio.coeffs()]
    calibration += [arb(0)]*(PREC-len(calibration))
    qseries = arb_series(calibration, PREC)
    calibrated_pilot = dict(pilot)
    calibrated_pilot["KF"] = pilot["KF"]-qseries*pilot["KD"]
    calibrated_pilot["HDF"] = pilot["HDF"]-qseries*pilot["HDD"]
    weights = terminal_weights(
        calibrated_pilot, delta, target_order=target_order,
        evaluation_ball=evaluation_ball)
    heap = []
    serial = 0

    def push(slo, shi, alo, ahi):
        nonlocal serial
        values = centered_cell(delta, t, slo, shi, alo, ahi,
                               calibration=calibration)
        score = sum(weights[name, order]*float(value.rad())
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
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    for *_, values in heap:
        for name, coefficients in values.items():
            for order, value in enumerate(coefficients):
                totals[name][order] += value
    moments = {name: arb_series(values, PREC)
               for name, values in totals.items()}
    return moments, len(heap), weights


def adaptive_y_series(delta: arb, t: arb, max_cells: int = 4096,
                      target_order: int = 3,
                      evaluation_ball: arb | None = None):
    moments, cells, weights = adaptive_moments(
        delta, t, max_cells=max_cells, target_order=target_order,
        evaluation_ball=evaluation_ball)
    return assemble_y(moments, delta), moments, cells, weights


def check() -> None:
    ctx.prec = 140
    delta, t = hull(arb("0.049"), arb("0.05")), arb("2.9")
    for grid in (24, 48):
        y, moments = normalized_y_series(delta, t, grid)
        print("grid", grid, "KD", moments["KD"].coeffs()[0].str(8),
              "Y3", y.coeffs()[3].str(10))
    print("POSITIVE PHYSICAL SERIES DESIGN ONLY")


if __name__ == "__main__":
    check()
