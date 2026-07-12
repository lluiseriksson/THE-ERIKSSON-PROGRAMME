"""Design integration of the regular delta=0 carrier on the fixed core.

This measures interval contraction only.  The complementary 1-chi integral
is deliberately absent, so no output of this file is a K2 certificate.
"""

import heapq

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
from surface_bessel_integral_remainder import relative_enclosure_invz
from surface_remainder_centered_prefactor import Dual, dadd, dmul, unary
from surface_remainder_core_l2_arb import (
    cutoff_dual, linear_first_moment, linear_integral,
)
from surface_remainder_delta0_geometry import regular_geometry_dual
from surface_remainder_delta0_moments import regular_moment_integrands


NAMES = ("kd", "kf_over_delta", "hdd_over_delta2", "hdf_over_delta3")


def dual_power(value: Dual, power: arb) -> Dual:
    return unary(value, value.v**power, power*value.v**(power-1),
                 power*(power-1)*value.v**(power-2))


def geometric_prefactors(delta: arb, t: arb, sigma: Dual,
                         tau: Dual) -> tuple[dict[str, Dual], object]:
    geometry = regular_geometry_dual(delta, t, sigma, tau)
    c = (t/4).cos(); common = 1/(arb(2)*arb.pi()).sqrt()
    kernel = dmul(2*common/(4*c)**(arb(3)/2),
                  dual_power(geometry.root, -arb(3)/2))
    h_regular = dmul(common/(4*c)**(arb(5)/2),
                     dual_power(geometry.root, -arb(5)/2))
    return {
        "kd": dmul(kernel, geometry.d_weight),
        "kf_over_delta": dmul(kernel, geometry.f_over_delta),
        "hdd_over_delta2": dmul(h_regular, dmul(
            geometry.d_weight, geometry.d_weight)),
        "hdf_over_delta3": dmul(h_regular, dmul(
            geometry.d_weight, geometry.f_over_delta)),
    }, geometry


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
                  alo: arb, ahi: arb,
                  calibration: arb | None = None,
                  complement: bool = False) -> dict[str, arb]:
    sigma, tau = hull(slo, shi), hull(alo, ahi)
    sm, am = (slo+shi)/2, (alo+ahi)/2
    sw, tw = shi-slo, ahi-alo
    cutoff = cutoff_dual(
        Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1))).v
    if complement:
        cutoff = 1-cutoff
    center_g, center_geometry = geometric_prefactors(
        delta, t, Dual(sm, arb(1)), Dual(am, arb(0), arb(1)))
    box_g, box_geometry = geometric_prefactors(
        delta, t, Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1)))
    names = NAMES
    if calibration is not None:
        center_g = dict(center_g); box_g = dict(box_g)
        center_g["kn"] = dadd(
            center_g["kf_over_delta"], dmul(-calibration, center_g["kd"]))
        center_g["gn"] = dadd(
            center_g["hdf_over_delta3"],
            dmul(-calibration, center_g["hdd_over_delta2"]))
        box_g["kn"] = dadd(
            box_g["kf_over_delta"], dmul(-calibration, box_g["kd"]))
        box_g["gn"] = dadd(
            box_g["hdf_over_delta3"],
            dmul(-calibration, box_g["hdd_over_delta2"]))
        names = ("kd", "kn", "hdd_over_delta2", "gn")
    pc, pb = center_geometry.phase, box_geometry.phase
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
    first_sigma = linear_first_moment(gs, sw)*linear_integral(gt, tw)
    first_tau = linear_integral(gs, sw)*linear_first_moment(gt, tw)
    phase_error = exp_remainder-1
    if box_geometry.inv_z.v.upper() <= arb(1)/20:
        order, z0 = 4, 20
    elif box_geometry.inv_z.v.upper() <= arb(1)/4:
        order, z0 = 0, 4
    else:
        raise ValueError("regular Bessel lane falls below z=4; subdivide")
    relatives = {
        "A": relative_enclosure_invz(box_geometry.inv_z.v, "A", order, z0),
        "B": relative_enclosure_invz(box_geometry.inv_z.v, "B", order, z0),
    }
    out = {}
    for name in names:
        gc, gb = center_g[name], box_g[name]
        affine = gc.v*spatial+gc.x*first_sigma+gc.y*first_tau
        hessian = (arb(gb.xx.abs_upper())*rx**2/2
                   +arb(gb.xy.abs_upper())*rx*ry
                   +arb(gb.yy.abs_upper())*ry**2/2)
        affine_abs = (arb(gc.v.abs_upper())
                      +arb(gc.x.abs_upper())*rx
                      +arb(gc.y.abs_upper())*ry)
        error = (hessian*exp_remainder+affine_abs*phase_error)*spatial
        family = "A" if name in ("kd", "kf_over_delta", "kn") else "B"
        out[name] = (pc.v.exp()*relatives[family]
                     *(affine+error*arb("0 +/- 1"))*4*cutoff)
    return out


def integrate_core_centered(delta: arb, t: arb, grid: int,
                            max_depth: int = 7,
                            calibration: arb | None = None,
                            complement: bool = False,
                            side_value: int = 10) -> dict[str, arb]:
    names = ("kd", "kn", "hdd_over_delta2", "gn") \
        if calibration is not None else NAMES
    totals = {name: arb(0) for name in names}
    width = arb(side_value)/grid
    stack = [(width*i, width*(i+1), width*j, width*(j+1), 0)
             for i in range(grid) for j in range(grid)]
    while stack:
        slo, shi, alo, ahi, depth = stack.pop()
        if not complement and slo**2+alo**2 >= 100:
            continue
        if complement and shi**2+ahi**2 <= 16:
            continue
        try:
            values = centered_cell(
                delta, t, slo, shi, alo, ahi, calibration=calibration,
                complement=complement)
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
        for name in names:
            totals[name] += values[name]
    return totals


def integrate_complement_centered(delta: arb, t: arb, grid: int,
                                  max_depth: int = 7,
                                  calibration: arb | None = None
                                  ) -> dict[str, arb]:
    """Integrate (1-chi) on the fixed [0,12]^2 endpoint square."""
    return integrate_core_centered(
        delta, t, grid, max_depth=max_depth, calibration=calibration,
        complement=True, side_value=12)


def adaptive_bilinear_centered(
    delta: arb, t: arb, max_cells: int = 4096, seed_grid: int = 4,
    complement: bool = False,
) -> tuple[dict[str, arb], int]:
    """Refine cells by their first-order impact on the centered bilinear."""
    c = (t/4).cos(); cc = 2*c**2-1
    calibration = -(2*cc+1)/(2*c)
    side = arb(12 if complement else 10)
    pilot = integrate_core_centered(
        delta, t, 8, calibration=calibration, complement=complement,
        side_value=12 if complement else 10)
    weights = {
        "kd": abs(float(pilot["gn"].mid())),
        "kn": abs(float(pilot["hdd_over_delta2"].mid())),
        "hdd_over_delta2": abs(float(pilot["kn"].mid())),
        "gn": abs(float(pilot["kd"].mid())),
    }
    heap = []
    serial = 0

    def push(slo, shi, alo, ahi):
        nonlocal serial
        if not complement and slo**2+alo**2 >= 100:
            return
        if complement and shi**2+ahi**2 <= 16:
            return
        values = centered_cell(
            delta, t, slo, shi, alo, ahi, calibration=calibration,
            complement=complement)
        score = sum(weights[name]*float(values[name].rad()) for name in values)
        heapq.heappush(heap, (-score, serial, slo, shi, alo, ahi, values))
        serial += 1

    width = side/seed_grid
    for i in range(seed_grid):
        for j in range(seed_grid):
            push(width*i, width*(i+1), width*j, width*(j+1))
    while heap and len(heap)+3 <= max_cells:
        _, _, slo, shi, alo, ahi, _ = heapq.heappop(heap)
        sm, am = (slo+shi)/2, (alo+ahi)/2
        push(slo, sm, alo, am); push(sm, shi, alo, am)
        push(slo, sm, am, ahi); push(sm, shi, am, ahi)
    totals = {name: arb(0) for name in ("kd", "kn", "hdd_over_delta2", "gn")}
    for *_, values in heap:
        for name in totals:
            totals[name] += values[name]
    return totals, len(heap)


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
    c = (arb("2.9")/4).cos(); cc = 2*c**2-1
    calibration = -(2*cc+1)/(2*c)
    for grid in (8, 16, 32):
        values = integrate_core_centered(
            delta, arb("2.9"), grid, calibration=calibration)
        bilinear = (values["kd"]*values["gn"]
                    -values["kn"]*values["hdd_over_delta2"])
        print("bilinear-centered", grid,
              {name: value.str(8) for name, value in values.items()},
              "B", bilinear.str(8))
    for grid in (8, 16):
        values = integrate_complement_centered(
            delta, arb("2.9"), grid, calibration=calibration)
        bilinear = (values["kd"]*values["gn"]
                    -values["kn"]*values["hdd_over_delta2"])
        print("complement-centered", grid,
              {name: value.str(8) for name, value in values.items()},
              "B", bilinear.str(8))
    for cells in (1024, 4096):
        values, effective = adaptive_bilinear_centered(
            delta, arb("2.9"), max_cells=cells)
        bilinear = (values["kd"]*values["gn"]
                    -values["kn"]*values["hdd_over_delta2"])
        print("adaptive-core", effective,
              {name: value.str(8) for name, value in values.items()},
              "B", bilinear.str(8))
    print("DELTA0 CORE [0,1/100] FINITE; DESIGN ONLY; COMPLETION OPEN")


if __name__ == "__main__":
    check()
