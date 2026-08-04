"""Exact delta-eight transport for the seven literal S1''' carriers.

The main and mirror saddle carriers are integrated on their fixed physical
quadrants.  Each delta coefficient uses the degree-four spatial Taylor
integrator and total-degree-five remainder from the S2 successor lane.

This is design infrastructure only.  It does not include the analytic
``delta=0`` patch or the nonlocal completion, and it carries no K4, S1''',
G1, G2, G6, or Surface Theorem promotion.
"""

from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction

from flint import arb, arb_series, ctx

import surface_remainder_s2_delta8_exact as base
from surface_remainder_arb_jet2 import hull
from surface_remainder_positive_physical_spatial3 import linear_moment
from surface_remainder_spatial_jet3 import (
    Jet3,
    jadd,
    jcos,
    jexp,
    jmul,
    jneg,
    jscale,
    jsin,
    jsqrt,
    jet,
    variable_x,
    variable_y,
)


MAIN_NAMES = ("muF_main", "nuD_main", "nuF_main")
MIRROR_NAMES = ("MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror")
NAMES = MAIN_NAMES + MIRROR_NAMES

BUDGETS = {
    "MD_mirror": "56.801",
    "MF_mirror": "156.28",
    "MD2r_mirror": "12.577",
    "MDFr_mirror": "44.352",
    "muF_main": "26.467",
    "nuD_main": "0.94119",
    "nuF_main": "8.1751",
}
DELTA_FINAL = Fraction(1, 15)


def _apply_radius_floor(radius2: Jet3, floor: arb) -> Jet3:
    if not floor > 0:
        raise ValueError("S1 radius floor must be strictly positive")
    coefficients = dict(radius2.coefficients)
    value = radius2.get(0, 0)
    coefficients[0, 0] = value.intersection(hull(floor, arb(value.upper())))
    return Jet3(coefficients)


def main_carrier_parts(
    delta: arb, t: arb, s: Jet3, alpha: Jet3
) -> tuple[dict[str, list[Jet3]], list[Jet3]]:
    """Judge-scaled main carriers before the common exponential."""

    moments, phase = base.physical_moment_parts(delta, t, s, alpha)
    ds = [jet(delta), jet(1)] + [jet(0) for _ in range(base.PREC - 2)]
    beta = base.sinv(ds)
    beta2 = base.smul(beta, beta)
    beta3 = base.smul(beta2, beta)
    return {
        "muF_main": base.smul(beta, moments["KF"]),
        "nuD_main": base.smul(beta2, moments["HDD"]),
        "nuF_main": base.smul(beta3, moments["HDF"]),
    }, phase


def mirror_carrier_parts(
    delta: arb, t: arb, sd: Jet3, ad: Jet3
) -> tuple[dict[str, list[Jet3]], list[Jet3]]:
    """Judge-scaled mirror carriers before the common exponential."""

    ds = [jet(delta), jet(1)] + [jet(0) for _ in range(base.PREC - 2)]
    beta = base.sinv(ds)
    beta2 = base.smul(beta, beta)
    beta_sqrt = base.ssqrt(beta)
    c, s4 = (t / 4).cos(), (t / 4).sin()
    pd = jmul(
        jsin(jscale(sd, arb(1) / 2)),
        jsin(jscale(sd, arb(1) / 2)),
    )
    qd = jmul(
        jsin(jscale(ad, arb(1) / 2)),
        jsin(jscale(ad, arb(1) / 2)),
    )
    ps, pa = jadd(1, jneg(pd)), jadd(1, jneg(qd))
    radius2 = jadd(
        jscale(jmul(ps, pa), 4 * s4**2),
        jscale(jmul(pd, qd), 4 * c**2),
    )
    u = arb("0.6").sin() ** 2
    mirror_floor = 4 * arb((s4**2).lower()) * (1 - u) ** 2
    radius = jsqrt(_apply_radius_floor(radius2, mirror_floor))
    z = base.sscale(beta, jscale(radius, 2))
    a_scaled = base._analytic_series(z, "A")
    b_scaled = base._analytic_series(z, "B")
    kernel = base.sscale(base.smul(beta2, beta_sqrt), 2)
    kernel = base.smul(kernel, a_scaled)
    hkernel = base.smul(base.smul(beta, beta_sqrt), b_scaled)
    dweight = jscale(jadd(1, jneg(jadd(ps, pa))), 2)
    cc = 2 * c**2 - 1
    x, y = jcos(sd), jcos(ad)
    fluctuation = jmul(
        jadd(x, 1),
        jadd(
            jscale(jadd(jscale(x, 2), -1), cc),
            jmul(y, jadd(1 + cc, jneg(x))),
        ),
    )
    phase = base.sscale(beta, jadd(jscale(radius, 2), -4 * s4))
    return {
        "MD_mirror": base.sscale(kernel, dweight),
        "MF_mirror": base.sscale(kernel, fluctuation),
        "MD2r_mirror": base.smul(
            beta2, base.sscale(hkernel, jmul(dweight, dweight))
        ),
        "MDFr_mirror": base.smul(
            beta2, base.sscale(hkernel, jmul(dweight, fluctuation))
        ),
    }, phase


def _remove_constant_and_linear(phase: Jet3, gx: arb, gy: arb) -> Jet3:
    coefficients = dict(phase.coefficients)
    coefficients[0, 0] = arb(0)
    coefficients[1, 0] = phase.get(1, 0) - gx
    coefficients[0, 1] = phase.get(0, 1) - gy
    return Jet3(coefficients)


def _centered_side(
    side: str,
    delta: arb,
    t: arb,
    slo: arb,
    shi: arb,
    alo: arb,
    ahi: arb,
) -> dict[str, list[arb]]:
    sm, am = (slo + shi) / 2, (alo + ahi) / 2
    rx, ry = (shi - slo) / 2, (ahi - alo) / 2
    parts = main_carrier_parts if side == "main" else mirror_carrier_parts
    names = MAIN_NAMES if side == "main" else MIRROR_NAMES
    center_pref, center_phase = parts(
        delta, t, variable_x(sm), variable_y(am)
    )
    box_pref, box_phase = parts(
        delta,
        t,
        variable_x(hull(slo, shi)),
        variable_y(hull(alo, ahi)),
    )
    center_correction = [jet(0)] + center_phase[1:]
    box_correction = [jet(0)] + box_phase[1:]
    center_values = {
        name: base.smul(value, base.sexp(center_correction))
        for name, value in center_pref.items()
    }
    box_values = {
        name: base.smul(value, base.sexp(box_correction))
        for name, value in box_pref.items()
    }
    phase0, phase0_box = center_phase[0], box_phase[0]
    gx = arb(phase0.get(1, 0).mid())
    gy = arb(phase0.get(0, 1).mid())
    center_residual = jexp(_remove_constant_and_linear(phase0, gx, gy))
    box_residual = jexp(_remove_constant_and_linear(phase0_box, gx, gy))
    mx = [linear_moment(gx, 2 * rx, order) for order in range(5)]
    my = [linear_moment(gy, 2 * ry, order) for order in range(5)]
    mass = mx[0] * my[0]
    out: dict[str, list[arb]] = {}
    for name in names:
        coefficients: list[arb] = []
        for center_coefficient, box_coefficient in zip(
            center_values[name], box_values[name]
        ):
            retained_spatial = jmul(center_coefficient, center_residual)
            whole_spatial = jmul(box_coefficient, box_residual)
            retained = arb(0)
            for degree in range(5):
                for i in range(degree + 1):
                    j = degree - i
                    retained += retained_spatial.get(i, j) * mx[i] * my[j]
            error = arb(0)
            for i in range(6):
                for j in range(6 - i):
                    if i + j == 5:
                        error += (
                            arb(whole_spatial.get(i, j).abs_upper())
                            * rx**i
                            * ry**j
                            * mass
                        )
            coefficients.append(
                4
                * phase0.get(0, 0).exp()
                * (retained + error * arb("0 +/- 1"))
            )
        out[name] = coefficients
    return out


def centered_cell(
    delta: arb,
    t: arb,
    slo: arb,
    shi: arb,
    alo: arb,
    ahi: arb,
) -> dict[str, list[arb]]:
    out = _centered_side("main", delta, t, slo, shi, alo, ahi)
    out.update(_centered_side("mirror", delta, t, slo, shi, alo, ahi))
    return out


def uniform_carriers(
    delta: arb,
    t: arb,
    grid: int,
    mesh_power: int | Fraction = 1,
) -> dict[str, list[arb]]:
    totals = {name: [arb(0) for _ in range(base.PREC)] for name in NAMES}
    nodes = base.spatial_nodes(grid, mesh_power)
    for i in range(grid):
        for j in range(grid):
            values = centered_cell(
                delta, t, nodes[i], nodes[i + 1], nodes[j], nodes[j + 1]
            )
            for name in NAMES:
                for order, value in enumerate(values[name]):
                    totals[name][order] += value
    return totals


def _row_worker(arguments):
    (
        precision,
        delta_wire,
        t_wire,
        grid,
        row_start,
        row_stop,
        mesh_power,
    ) = arguments
    ctx.prec = precision
    delta, t = base._unwire_arb(delta_wire), base._unwire_arb(t_wire)
    totals = {name: [arb(0) for _ in range(base.PREC)] for name in NAMES}
    nodes = base.spatial_nodes(grid, mesh_power)
    for i in range(row_start, row_stop):
        for j in range(grid):
            values = centered_cell(
                delta, t, nodes[i], nodes[i + 1], nodes[j], nodes[j + 1]
            )
            for name in NAMES:
                for order, value in enumerate(values[name]):
                    totals[name][order] += value
    return {
        name: base._wire_series(values) for name, values in totals.items()
    }


def parallel_uniform_carriers(
    delta: arb,
    t: arb,
    grid: int,
    workers: int = 4,
    mesh_power: int | Fraction = 1,
) -> dict[str, list[arb]]:
    if workers < 1 or grid % workers:
        raise ValueError("grid must be divisible by the positive worker count")
    step = grid // workers
    arguments = [
        (
            ctx.prec,
            base._wire_arb(delta),
            base._wire_arb(t),
            grid,
            worker * step,
            (worker + 1) * step,
            mesh_power,
        )
        for worker in range(workers)
    ]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        pieces = list(executor.map(_row_worker, arguments))
    totals = {name: [arb(0) for _ in range(base.PREC)] for name in NAMES}
    for piece in pieces:
        for name in NAMES:
            for order, value in enumerate(base._unwire_series(piece[name])):
                totals[name][order] += value
    return totals


def _half_second_transport(
    center_coefficients: list[arb],
    box_coefficients: list[arb],
    radius: arb,
) -> arb:
    perturbation = hull(-radius, radius)
    retained = arb(0)
    for order in reversed(range(2, 8)):
        retained = retained * perturbation
        retained += arb(order * (order - 1)) * center_coefficients[order] / 2
    remainder = (
        arb(28) * arb(box_coefficients[8].abs_upper()) * radius**6
    )
    return retained + remainder * arb("0 +/- 1")


def centered_half_second_enclosures(
    delta_lo: arb,
    delta_hi: arb,
    t: arb,
    center_grid: int,
    remainder_grid: int,
    workers: int = 4,
    center_mesh_power: int | Fraction = 1,
    remainder_mesh_power: int | Fraction = 1,
) -> tuple[dict[str, arb], dict[str, arb_series], dict[str, arb_series]]:
    if not arb(0) < delta_lo <= delta_hi:
        raise ValueError("S1 delta-eight box must be positive and ordered")
    center, radius = (delta_lo + delta_hi) / 2, (delta_hi - delta_lo) / 2

    def integrate(delta_value, grid, mesh_power):
        if workers == 1:
            return uniform_carriers(delta_value, t, grid, mesh_power)
        return parallel_uniform_carriers(
            delta_value, t, grid, workers=workers, mesh_power=mesh_power
        )

    center_raw = integrate(center, center_grid, center_mesh_power)
    box_raw = integrate(
        hull(delta_lo, delta_hi), remainder_grid, remainder_mesh_power
    )
    center_series = {
        name: arb_series(values, base.PREC)
        for name, values in center_raw.items()
    }
    box_series = {
        name: arb_series(values, base.PREC)
        for name, values in box_raw.items()
    }
    enclosures = {}
    for name in NAMES:
        center_coefficients = center_series[name].coeffs() + [arb(0)] * base.PREC
        box_coefficients = box_series[name].coeffs() + [arb(0)] * base.PREC
        enclosures[name] = _half_second_transport(
            center_coefficients, box_coefficients, radius
        )
    return enclosures, center_series, box_series


def single_box_fractions(
    half_second: dict[str, arb], delta_lo: arb, delta_hi: arb
) -> dict[str, arb]:
    delta_final = arb(DELTA_FINAL.numerator) / DELTA_FINAL.denominator
    weight = (
        delta_final * (delta_hi - delta_lo)
        - (delta_hi**2 - delta_lo**2) / 2
    )
    return {
        name: (
            2
            * arb(value.abs_upper())
            * weight
            / (arb(BUDGETS[name]) * delta_final**2)
        )
        for name, value in half_second.items()
    }


def check() -> None:
    assert set(BUDGETS) == set(NAMES)
    assert all(arb(BUDGETS[name]) > 0 for name in NAMES)
    print("S1 exact delta-eight/spatial-five infrastructure OK; no promotion")


if __name__ == "__main__":
    check()
