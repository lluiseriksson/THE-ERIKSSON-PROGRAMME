"""Design integration of the regular delta=0 carrier on the fixed core.

This measures interval contraction only.  The complementary 1-chi integral
is deliberately absent, so no output of this file is a K2 certificate.
"""

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_centered_prefactor import Dual
from surface_remainder_core_l2_arb import cutoff_dual, linear_integral
from surface_remainder_delta0_geometry import regular_phase_dual
from surface_remainder_delta0_moments import (
    regular_moment_integrands, regular_moment_parts,
)


NAMES = ("kd", "kf_over_delta", "hdd_over_delta2", "hdf_over_delta3")


def integrate_core(delta: arb, t: arb, grid: int,
                   max_depth: int = 7) -> dict[str, arb]:
    totals = {name: arb(0) for name in NAMES}
    side = arb(10)
    width = side/grid
    stack = [(width*i, width*(i+1), width*j, width*(j+1), 0)
             for i in range(grid) for j in range(grid)]
    while stack:
        slo, shi, alo, ahi, depth = stack.pop()
        if slo**2+alo**2 >= 100:
            continue
        sigma, tau = hull(slo, shi), hull(alo, ahi)
        cutoff = cutoff_dual(
            Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1))).v
        if cutoff == 0:
            continue
        try:
            moments = regular_moment_integrands(delta, t, sigma, tau)
        except ValueError:
            if depth >= max_depth:
                raise
            sm, am = (slo+shi)/2, (alo+ahi)/2
            stack.extend([
                (slo, sm, alo, am, depth+1),
                (sm, shi, alo, am, depth+1),
                (slo, sm, am, ahi, depth+1),
                (sm, shi, am, ahi, depth+1),
            ])
            continue
        area = (shi-slo)*(ahi-alo)*4
        for name in NAMES:
            totals[name] += getattr(moments, name)*cutoff*area
    return totals


def centered_cell(delta: arb, t: arb, slo: arb, shi: arb,
                  alo: arb, ahi: arb) -> dict[str, arb]:
    sigma, tau = hull(slo, shi), hull(alo, ahi)
    sm, am = (slo+shi)/2, (alo+ahi)/2
    sw, tw = shi-slo, ahi-alo
    cutoff = cutoff_dual(
        Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1))).v
    prefactors, _ = regular_moment_parts(delta, t, sigma, tau)
    pc = regular_phase_dual(
        delta, t, Dual(sm, arb(1)), Dual(am, arb(0), arb(1)))
    pb = regular_phase_dual(
        delta, t, Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1)))
    gs, gt = arb(pc.x.mid()), arb(pc.y.mid())
    rx, ry = sw/2, tw/2
    radius = (
        arb((pc.x-gs).abs_upper())*rx
        +arb((pc.y-gt).abs_upper())*ry
        +arb(pb.xx.abs_upper())*rx**2/2
        +arb(pb.xy.abs_upper())*rx*ry
        +arb(pb.yy.abs_upper())*ry**2/2
    )
    exp_remainder = (radius*arb("0 +/- 1")).exp()
    spatial = linear_integral(gs, sw)*linear_integral(gt, tw)
    common = pc.v.exp()*exp_remainder*spatial*4*cutoff
    return {name: getattr(prefactors, name)*common for name in NAMES}


def integrate_core_centered(delta: arb, t: arb, grid: int,
                            max_depth: int = 7) -> dict[str, arb]:
    totals = {name: arb(0) for name in NAMES}
    width = arb(10)/grid
    stack = [(width*i, width*(i+1), width*j, width*(j+1), 0)
             for i in range(grid) for j in range(grid)]
    while stack:
        slo, shi, alo, ahi, depth = stack.pop()
        if slo**2+alo**2 >= 100:
            continue
        try:
            values = centered_cell(delta, t, slo, shi, alo, ahi)
        except ValueError:
            if depth >= max_depth:
                raise
            sm, am = (slo+shi)/2, (alo+ahi)/2
            stack.extend([
                (slo, sm, alo, am, depth+1),
                (sm, shi, alo, am, depth+1),
                (slo, sm, am, ahi, depth+1),
                (sm, shi, am, ahi, depth+1),
            ])
            continue
        for name in NAMES:
            totals[name] += values[name]
    return totals


def check() -> None:
    ctx.prec = 140
    # A single [0,1/20] natural interval is rejected: delta dependency leaves
    # the outer root unresolved even after spatial refinement.  The analytic
    # endpoint pilot therefore measures only the born interval [0,1/100].
    delta = hull(arb(0), arb(1)/100)
    for grid in (8, 16, 32):
        values = integrate_core(delta, arb("2.9"), grid)
        assert all(value.is_finite() for value in values.values())
        print("grid", grid, {name: value.str(8) for name, value in values.items()})
    for grid in (8, 16, 32):
        values = integrate_core_centered(delta, arb("2.9"), grid)
        assert all(value.is_finite() for value in values.values())
        print("centered", grid,
              {name: value.str(8) for name, value in values.items()})
    print("DELTA0 CORE [0,1/100] FINITE; DESIGN ONLY; COMPLETION OPEN")


if __name__ == "__main__":
    check()
