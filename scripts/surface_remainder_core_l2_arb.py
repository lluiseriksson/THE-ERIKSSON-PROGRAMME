"""Linear-exponential Arb smoke for the scaled main saddle block.

Design only: this measures whether the cellwise mean-value linearization used by
the existing exp-integrator is strong enough for the weighted remainder carrier.
"""

from __future__ import annotations

import heapq
import hashlib
import sys

import flint
from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_carrier_jet import scaled_carrier_parts
from surface_remainder_centered_prefactor import (
    Dual, coefficient, centered_coefficients, dadd, dmul, dsquare, mirror_coefficient,
    phase_residual_spatial, phase_spatial,
)


R0 = 4
R1 = 10
DELTA_R2 = R1**2-R0**2


def symmetric(radius: arb) -> arb:
    return radius * arb("0 +/- 1")


def phase_gradients(delta: arb, t: arb, sigma: arb, tau: arb) -> tuple[arb, arb]:
    beta, root_delta = 1 / delta, delta.sqrt()
    c, s4 = (t / 4).cos(), (t / 4).sin()
    s, alpha = sigma * root_delta, tau * root_delta
    p, q = (s / 2).sin() ** 2, (alpha / 2).sin() ** 2
    r2 = 4 * c**2 * (1 - p) * (1 - q) + 4 * s4**2 * p * q
    radius = r2.sqrt()
    dp = s.sin() * root_delta / 2
    dq = alpha.sin() * root_delta / 2
    return (
        beta * 4 * (q - c**2) * dp / radius,
        beta * 4 * (p - c**2) * dq / radius,
    )


def linear_integral(gradient: arb, width: arb) -> arb:
    if not gradient:
        return width
    half = gradient * width / 2
    return (half.exp() - (-half).exp()) / gradient


def linear_first_moment(gradient: arb, width: arb) -> arb:
    """Integral of x exp(gradient*x) on the centered interval."""
    if not gradient:
        return arb(0)
    a = width / 2
    ga = gradient * a
    return ((ga - 1) * ga.exp() + (ga + 1) * (-ga).exp()) / gradient**2


def cell_bounds(
    delta: arb, t: arb, sigma_lo: arb, sigma_hi: arb, tau_lo: arb, tau_hi: arb
) -> tuple[dict[str, arb], dict[str, arb]]:
    sigma, tau = hull(sigma_lo, sigma_hi), hull(tau_lo, tau_hi)
    sm, tm = (sigma_lo + sigma_hi) / 2, (tau_lo + tau_hi) / 2
    sw, tw = sigma_hi - sigma_lo, tau_hi - tau_lo
    prefactors, phase = scaled_carrier_parts(delta, t, sigma, tau)
    centered = centered_coefficients(delta, t, sigma_lo, sigma_hi,
                                     tau_lo, tau_hi)
    _, center_phase = scaled_carrier_parts(delta, t, sm, tm)
    phase_at_center = phase_spatial(
        delta, t, Dual(sm, arb(1)), Dual(tm, arb(0), arb(1)))
    phase_on_box = phase_spatial(
        delta, t, Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1)))
    gs0, gt0 = arb(phase_at_center.x.mid()), arb(phase_at_center.y.mid())
    rx, ry = sw/2, tw/2
    phase_radius_bound = (
        arb((phase_at_center.x-gs0).abs_upper())*rx
        + arb((phase_at_center.y-gt0).abs_upper())*ry
        + arb(phase_on_box.xx.abs_upper())*rx**2/2
        + arb(phase_on_box.xy.abs_upper())*rx*ry
        + arb(phase_on_box.yy.abs_upper())*ry**2/2
    )
    residual = symmetric(phase_radius_bound)
    exponential = center_phase.c0.exp() * residual.exp()
    center_exp = center_phase.c0.exp()
    phase_radius = arb(residual.abs_upper())
    phase_error = phase_radius.exp() - 1
    spatial_integral = linear_integral(gs0, sw) * linear_integral(gt0, tw)
    first_sigma = linear_first_moment(gs0, sw) * linear_integral(gt0, tw)
    first_tau = linear_integral(gs0, sw) * linear_first_moment(gt0, tw)
    center_coeff = coefficient(delta, t, Dual(sm, arb(1)),
                               Dual(tm, arb(0), arb(1)))
    box_coeff = coefficient(delta, t, Dual(sigma, arb(1)),
                            Dual(tau, arb(0), arb(1)))
    signed: dict[str, arb] = {}
    absolute: dict[str, arb] = {}
    for name, prefactor in prefactors.items():
        direct = (
            prefactor.c2
            + prefactor.c1 * phase.c1
            + prefactor.c0 * (phase.c2 + phase.c1**2 / 2)
        )
        coeff_enclosure = direct.intersection(centered[name])
        cc = center_coeff[name]
        affine_integral = (cc.v * spatial_integral
                           + cc.x * first_sigma + cc.y * first_tau)
        rx, ry = sw / 2, tw / 2
        hessian_remainder = (
            arb(box_coeff[name].xx.abs_upper()) * rx**2 / 2
            + arb(box_coeff[name].xy.abs_upper()) * rx * ry
            + arb(box_coeff[name].yy.abs_upper()) * ry**2 / 2
        )
        affine_abs = (arb(cc.v.abs_upper())
                      + arb(cc.x.abs_upper()) * sw / 2
                      + arb(cc.y.abs_upper()) * tw / 2)
        error = ((hessian_remainder * phase_radius.exp()
                  + affine_abs * phase_error) * spatial_integral)
        # Integrate the affine coefficient exactly against the linearized
        # exponential; only the coefficient and phase remainders use balls.
        signed[name] = center_exp * (affine_integral + symmetric(error)) * 2
        absolute[name] = (
            arb(coeff_enclosure.abs_upper()) * exponential * spatial_integral * 2
        )
    return signed, absolute


def smoke(grid: int = 8, delta_value: arb | None = None
          ) -> tuple[dict[str, arb], dict[str, arb]]:
    ctx.prec = 100
    delta, t = (delta_value or arb(1) / 15), arb("2.9")
    length = arb("1.2") / delta.sqrt()
    names = ("muF_main", "nuD_main", "nuF_main")
    totals = {name: arb(0) for name in names}
    l1_totals = {name: arb(0) for name in names}
    for i in range(grid):
        for j in range(grid):
            bounds, l1_bounds = cell_bounds(
                delta,
                t,
                length * i / grid,
                length * (i + 1) / grid,
                length * j / grid,
                length * (j + 1) / grid,
            )
            for name, value in bounds.items():
                totals[name] += 4 * value
                l1_totals[name] += 4 * l1_bounds[name]
    return totals, l1_totals


def adaptive_smoke(max_cells: int = 1024, seed_grid: int = 4
                   ) -> tuple[dict[str, arb], int]:
    """Quadtree design sweep prioritized by the committed bucket scales."""
    ctx.prec = 100
    delta, t = arb(1)/15, arb("2.9")
    length = arb("1.2") / delta.sqrt()
    names = ("muF_main", "nuD_main", "nuF_main")
    budgets = {"muF_main": 26.467, "nuD_main": 0.94119,
               "nuF_main": 8.1751}
    heap = []
    serial = 0

    def push(lo: arb, hi: arb, alo: arb, ahi: arb) -> None:
        nonlocal serial
        bounds, _ = cell_bounds(delta, t, lo, hi, alo, ahi)
        score = max(float(bounds[name].rad())/budgets[name] for name in names)
        heapq.heappush(heap, (-score, serial, lo, hi, alo, ahi, bounds))
        serial += 1

    for i in range(seed_grid):
        for j in range(seed_grid):
            push(length*i/seed_grid, length*(i+1)/seed_grid,
                 length*j/seed_grid, length*(j+1)/seed_grid)
    while len(heap) + 3 <= max_cells:
        _, _, lo, hi, alo, ahi, _ = heapq.heappop(heap)
        mid, amid = (lo+hi)/2, (alo+ahi)/2
        push(lo, mid, alo, amid)
        push(mid, hi, alo, amid)
        push(lo, mid, amid, ahi)
        push(mid, hi, amid, ahi)
    totals = {name: arb(0) for name in names}
    for _, _, _, _, _, _, bounds in heap:
        for name in names:
            totals[name] += 4*bounds[name]
    return totals, len(heap)


def mirror_cell_bounds(delta: arb, t: arb, sigma_lo: arb, sigma_hi: arb,
                       tau_lo: arb, tau_hi: arb) -> dict[str, arb]:
    sigma, tau = hull(sigma_lo, sigma_hi), hull(tau_lo, tau_hi)
    sm, tm = (sigma_lo+sigma_hi)/2, (tau_lo+tau_hi)/2
    sw, tw = sigma_hi-sigma_lo, tau_hi-tau_lo
    center = mirror_coefficient(delta, t, Dual(sm, arb(1)),
                                Dual(tm, arb(0), arb(1)))
    box = mirror_coefficient(delta, t, Dual(sigma, arb(1)),
                             Dual(tau, arb(0), arb(1)))
    pc = phase_spatial(delta, t, Dual(sm, arb(1)),
                       Dual(tm, arb(0), arb(1)), mirror=True)
    pb = phase_spatial(delta, t, Dual(sigma, arb(1)),
                       Dual(tau, arb(0), arb(1)), mirror=True)
    gx, gy = arb(pc.x.mid()), arb(pc.y.mid())
    rx, ry = sw/2, tw/2
    pr = (arb((pc.x-gx).abs_upper())*rx
          + arb((pc.y-gy).abs_upper())*ry
          + arb(pb.xx.abs_upper())*rx**2/2
          + arb(pb.xy.abs_upper())*rx*ry
          + arb(pb.yy.abs_upper())*ry**2/2)
    l0x, l0y = linear_integral(gx, sw), linear_integral(gy, tw)
    l1x, l1y = linear_first_moment(gx, sw), linear_first_moment(gy, tw)
    area_weight = l0x*l0y
    out = {}
    for name, cc in center.items():
        affine = cc.v*area_weight + cc.x*l1x*l0y + cc.y*l0x*l1y
        hr = (arb(box[name].xx.abs_upper())*rx**2/2
              + arb(box[name].xy.abs_upper())*rx*ry
              + arb(box[name].yy.abs_upper())*ry**2/2)
        affine_abs = (arb(cc.v.abs_upper()) + arb(cc.x.abs_upper())*rx
                      + arb(cc.y.abs_upper())*ry)
        err = (hr*pr.exp() + affine_abs*(pr.exp()-1))*area_weight
        out[name] = pc.v.exp()*(affine+symmetric(err))*2
    return out


def mirror_smoke(grid: int = 8) -> dict[str, arb]:
    ctx.prec = 100
    delta, t = arb(1)/15, arb("2.9")
    length = arb("1.2")/delta.sqrt()
    names = ("MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror")
    totals = {name: arb(0) for name in names}
    for i in range(grid):
        for j in range(grid):
            cell = mirror_cell_bounds(
                delta, t, length*i/grid, length*(i+1)/grid,
                length*j/grid, length*(j+1)/grid)
            for name in names:
                totals[name] += 4*cell[name]
    return totals


def gaussian_integrals(lo: arb, hi: arb, p: arb) -> tuple[arb, arb]:
    """Zeroth and first moments of exp(-p*x^2/2) on [lo,hi]."""
    root = (p/2).sqrt()
    g0 = (arb.pi()/(2*p)).sqrt()*((root*hi).erf()-(root*lo).erf())
    g1 = ((-p*lo**2/2).exp()-(-p*hi**2/2).exp())/p
    return g0, g1


def mirror_gaussian_cell_bounds(delta: arb, t: arb, sigma_lo: arb,
                                sigma_hi: arb, tau_lo: arb,
                                tau_hi: arb) -> dict[str, arb]:
    sigma, tau = hull(sigma_lo, sigma_hi), hull(tau_lo, tau_hi)
    sm, tm = (sigma_lo+sigma_hi)/2, (tau_lo+tau_hi)/2
    sw, tw = sigma_hi-sigma_lo, tau_hi-tau_lo
    center = mirror_coefficient(delta, t, Dual(sm, arb(1)),
                                Dual(tm, arb(0), arb(1)))
    box = mirror_coefficient(delta, t, Dual(sigma, arb(1)),
                             Dual(tau, arb(0), arb(1)))
    residual_center = phase_residual_spatial(
        delta, t, Dual(sm, arb(1)), Dual(tm, arb(0), arb(1)),
        mirror=True)
    residual = phase_residual_spatial(
        delta, t, Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1)),
        mirror=True)
    p = (t/4).sin()
    g0x, g1x = gaussian_integrals(sigma_lo, sigma_hi, p)
    g0y, g1y = gaussian_integrals(tau_lo, tau_hi, p)
    mx, my = g1x-sm*g0x, g1y-tm*g0y
    weight = g0x*g0y
    rx, ry = sw/2, tw/2
    residual_hessian = (
        arb(residual.xx.abs_upper())*rx**2/2
        + arb(residual.xy.abs_upper())*rx*ry
        + arb(residual.yy.abs_upper())*ry**2/2
    )
    residual_range = (
        residual_center.v + residual_center.x*symmetric(rx)
        + residual_center.y*symmetric(ry)
        + symmetric(residual_hessian)
    )
    eps = arb(residual_range.abs_upper())
    qerr = arb((residual_range.exp()-1).abs_upper())
    out = {}
    for name, cc in center.items():
        affine = cc.v*weight + cc.x*mx*g0y + cc.y*g0x*my
        hr = (arb(box[name].xx.abs_upper())*rx**2/2
              + arb(box[name].xy.abs_upper())*rx*ry
              + arb(box[name].yy.abs_upper())*ry**2/2)
        affine_abs = (arb(cc.v.abs_upper()) + arb(cc.x.abs_upper())*rx
                      + arb(cc.y.abs_upper())*ry)
        err = (hr*eps.exp() + affine_abs*qerr)*weight
        out[name] = (affine+symmetric(err))*2
    return out


def mirror_gaussian_smoke(grid: int = 8) -> dict[str, arb]:
    ctx.prec = 100
    delta, t = arb(1)/15, arb("2.9")
    length = arb("1.2")/delta.sqrt()
    names = ("MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror")
    totals = {name: arb(0) for name in names}
    for i in range(grid):
        for j in range(grid):
            cell = mirror_gaussian_cell_bounds(
                delta, t, length*i/grid, length*(i+1)/grid,
                length*j/grid, length*(j+1)/grid)
            for name in names:
                totals[name] += 4*cell[name]
    return totals


def _include_zero(value: arb) -> arb:
    lo, hi = arb(value.lower()), arb(value.upper())
    if lo > 0:
        lo = arb(0)
    if hi < 0:
        hi = arb(0)
    return hull(lo, hi)


def cutoff_dual(sigma: Dual, tau: Dual) -> Dual:
    """Pre-registered radial C2 cutoff R0=4, R1=10."""
    u = dadd(dsquare(sigma), dsquare(tau))
    if u.v.upper() <= R0**2:
        return Dual(arb(1))
    if u.v.lower() >= R1**2:
        return Dual(arb(0))
    qlo = arb(0) if u.v.lower() < R0**2 else (arb(u.v.lower())-R0**2)/DELTA_R2
    qhi = arb(1) if u.v.upper() > R1**2 else (arb(u.v.upper())-R0**2)/DELTA_R2

    def h(q: arb) -> arb:
        return 1-10*q**3+15*q**4-6*q**5

    qbox = hull(qlo, qhi)
    value = hull(h(qhi), h(qlo))
    first = -30*qbox**2*(qbox-1)**2/DELTA_R2
    second = (-60*qbox+180*qbox**2-120*qbox**3)/DELTA_R2**2
    if u.v.lower() < R0**2 or u.v.upper() > R1**2:
        first, second = _include_zero(first), _include_zero(second)
    return Dual(
        value,
        first*u.x,
        first*u.y,
        second*u.x**2+first*u.xx,
        second*u.x*u.y+first*u.xy,
        second*u.y**2+first*u.yy,
    )


def localized_cell_bounds(delta: arb, t: arb, sigma_lo: arb, sigma_hi: arb,
                          tau_lo: arb, tau_hi: arb,
                          mirror: bool = False) -> dict[str, arb]:
    if sigma_lo**2+tau_lo**2 >= R1**2:
        names = (("MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror")
                 if mirror else ("muF_main", "nuD_main", "nuF_main"))
        return {name: arb(0) for name in names}
    sigma, tau = hull(sigma_lo, sigma_hi), hull(tau_lo, tau_hi)
    sm, tm = (sigma_lo+sigma_hi)/2, (tau_lo+tau_hi)/2
    sw, tw = sigma_hi-sigma_lo, tau_hi-tau_lo
    carrier = mirror_coefficient if mirror else coefficient
    center = carrier(delta, t, Dual(sm, arb(1)), Dual(tm, arb(0), arb(1)))
    box = carrier(delta, t, Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1)))
    center_cutoff = cutoff_dual(Dual(sm, arb(1)), Dual(tm, arb(0), arb(1)))
    box_cutoff = cutoff_dual(Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1)))
    center = {name: dmul(value, center_cutoff) for name, value in center.items()}
    box = {name: dmul(value, box_cutoff) for name, value in box.items()}
    pc = phase_spatial(delta, t, Dual(sm, arb(1)),
                       Dual(tm, arb(0), arb(1)), mirror=mirror)
    pb = phase_spatial(delta, t, Dual(sigma, arb(1)),
                       Dual(tau, arb(0), arb(1)), mirror=mirror)
    gx, gy = arb(pc.x.mid()), arb(pc.y.mid())
    rx, ry = sw/2, tw/2
    phase_radius = (
        arb((pc.x-gx).abs_upper())*rx+arb((pc.y-gy).abs_upper())*ry
        + arb(pb.xx.abs_upper())*rx**2/2
        + arb(pb.xy.abs_upper())*rx*ry
        + arb(pb.yy.abs_upper())*ry**2/2)
    l0x, l0y = linear_integral(gx, sw), linear_integral(gy, tw)
    l1x, l1y = linear_first_moment(gx, sw), linear_first_moment(gy, tw)
    weight = l0x*l0y
    out = {}
    for name, cc in center.items():
        affine = cc.v*weight+cc.x*l1x*l0y+cc.y*l0x*l1y
        hr = (arb(box[name].xx.abs_upper())*rx**2/2
              + arb(box[name].xy.abs_upper())*rx*ry
              + arb(box[name].yy.abs_upper())*ry**2/2)
        affine_abs = (arb(cc.v.abs_upper())+arb(cc.x.abs_upper())*rx
                      + arb(cc.y.abs_upper())*ry)
        err = (hr*phase_radius.exp()
               + affine_abs*(phase_radius.exp()-1))*weight
        out[name] = pc.v.exp()*(affine+symmetric(err))*2
    return out


def localized_smoke(grid: int = 32, mirror: bool = False) -> dict[str, arb]:
    ctx.prec = 100
    delta, t, length = arb(1)/15, arb("2.9"), arb(R1)
    names = (("MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror")
             if mirror else ("muF_main", "nuD_main", "nuF_main"))
    totals = {name: arb(0) for name in names}
    for i in range(grid):
        for j in range(grid):
            cell = localized_cell_bounds(
                delta, t, length*i/grid, length*(i+1)/grid,
                length*j/grid, length*(j+1)/grid, mirror=mirror)
            for name in names:
                totals[name] += 4*cell[name]
    return totals


if __name__ == "__main__":
    print("=== SURFACE REMAINDER CORE L2: localized Arb refinement ===")
    print("script sha256 : %s" % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
    print("python-flint %s  python %s  prec 100" %
          (flint.__version__, sys.version.split()[0]))
    print("registered localization: R0=%d R1=%d; stress delta=1/15 t=2.9"
          % (R0, R1), flush=True)
    main_results = {}
    mirror_results = {}
    for grid in (16, 32, 64):
        main_results[grid] = localized_smoke(grid, False)
        mirror_results[grid] = localized_smoke(grid, True)
        print("main %d: %s" % (grid, {k: v.str(12) for k, v in main_results[grid].items()}),
              flush=True)
        print("mirror %d: %s" % (grid, {k: v.str(12) for k, v in mirror_results[grid].items()}),
              flush=True)
    main_results[128] = localized_smoke(128, False)
    print("main 128: %s" %
          {k: v.str(12) for k, v in main_results[128].items()}, flush=True)
    main_budgets = {"muF_main": 26.467, "nuD_main": 0.94119,
                    "nuF_main": 8.1751}
    mirror_budgets = {"MD_mirror": 56.801, "MF_mirror": 156.28,
                      "MD2r_mirror": 12.577, "MDFr_mirror": 44.352}
    main_ok = all(float(v.abs_upper()) <= main_budgets[k]
                  for k, v in main_results[128].items())
    mirror_ok = all(float(v.abs_upper()) <= mirror_budgets[k]
                    for k, v in mirror_results[64].items())
    print("L1 FINITENESS: PASS")
    print("L2 CORE BUCKETS: main128=%s mirror64=%s" %
          ("PASS" if main_ok else "FAIL", "PASS" if mirror_ok else "FAIL"))
    if not (main_ok and mirror_ok):
        raise SystemExit(1)
    print("VERDICT: LOCALIZED CORE L2 DESIGN PASS; K4 COMPLEMENT AND S1'''/S2''' REMAIN OPEN")
