"""Exact order-eight delta transport for the literal S2''' judge.

The constant delta parameter is expanded as an Arb Taylor series through
degree eight.  Every coefficient is integrated with a degree-four spatial
Taylor polynomial and a total-degree-five remainder.  Scaled-Bessel
derivatives through order thirteen come from the exact recurrence in
``surface_remainder_s2_spatial5_exact``.

This remains design infrastructure until a frozen delta partition, analytic
zero patch, production/replay pair, provenance manifest, and literal weighted
sum are present.
"""

from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from math import factorial

from flint import arb, arb_series, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_positive_physical_spatial3 import linear_moment
from surface_remainder_s2_spatial5_exact import (
    _unwire_arb,
    _wire_arb,
    scaled_bessel_derivatives,
)
from surface_remainder_spatial_jet3 import (
    INDICES,
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


PREC = 9
NAMES = ("KD", "KF", "HDD", "HDF")


def sconst(value) -> list[Jet3]:
    return [jet(value)] + [jet(0) for _ in range(PREC - 1)]


def sadd(a: list[Jet3], b: list[Jet3]) -> list[Jet3]:
    return [jadd(x, y) for x, y in zip(a, b)]


def sneg(a: list[Jet3]) -> list[Jet3]:
    return [jneg(value) for value in a]


def sscale(a: list[Jet3], value) -> list[Jet3]:
    return [jscale(item, value) for item in a]


def smul(a: list[Jet3], b: list[Jet3]) -> list[Jet3]:
    out = [jet(0) for _ in range(PREC)]
    for order in range(PREC):
        for left in range(order + 1):
            out[order] = jadd(out[order], jmul(a[left], b[order - left]))
    return out


def sinv(a: list[Jet3]) -> list[Jet3]:
    from surface_remainder_spatial_jet3 import jinv

    out = [jet(0) for _ in range(PREC)]
    out[0] = jinv(a[0])
    for order in range(1, PREC):
        total = jet(0)
        for left in range(1, order + 1):
            total = jadd(total, jmul(a[left], out[order - left]))
        out[order] = jneg(jmul(out[0], total))
    return out


def ssqrt(a: list[Jet3]) -> list[Jet3]:
    out = [jet(0) for _ in range(PREC)]
    out[0] = jsqrt(a[0])
    for order in range(1, PREC):
        total = a[order]
        for left in range(1, order):
            total = jadd(total, jneg(jmul(out[left], out[order - left])))
        out[order] = jmul(total, sinv([jscale(out[0], 2)] + [jet(0)] * 8)[0])
    return out


def sexp(a: list[Jet3]) -> list[Jet3]:
    out = [jet(0) for _ in range(PREC)]
    out[0] = jexp(a[0])
    for order in range(1, PREC):
        total = jet(0)
        for left in range(1, order + 1):
            total = jadd(total, jscale(jmul(a[left], out[order - left]), left))
        out[order] = jscale(total, arb(1) / order)
    return out


def _spatial_outer(z: Jet3, family: str, base_order: int) -> Jet3:
    derivatives = scaled_bessel_derivatives(
        z.get(0, 0), family, base_order + 5
    )
    normalized = [
        derivatives[base_order + spatial_order] / arb(factorial(spatial_order))
        for spatial_order in range(6)
    ]
    increment = Jet3(
        {
            index: (arb(0) if index == (0, 0) else z.get(*index))
            for index in INDICES
        }
    )
    powers = [jet(1)]
    for _ in range(5):
        powers.append(jmul(powers[-1], increment))
    out = jet(0)
    for coefficient, power in zip(normalized, powers):
        out = jadd(out, jscale(power, coefficient))
    return out


def _analytic_series(z: list[Jet3], family: str) -> list[Jet3]:
    centre = z[0]
    increment = list(z)
    increment[0] = jet(0)
    powers = [sconst(1)]
    for _ in range(PREC - 1):
        powers.append(smul(powers[-1], increment))
    out = sconst(0)
    for order, power in enumerate(powers):
        derivative = _spatial_outer(centre, family, order)
        out = sadd(out, sscale(power, jscale(derivative, arb(1) / factorial(order))))
    return out


def _apply_radius_floor(radius2: Jet3) -> Jet3:
    u = arb("0.6").sin() ** 2
    floor = 2 * (1 - u) ** 2
    coefficients = dict(radius2.coefficients)
    value = radius2.get(0, 0)
    coefficients[0, 0] = value.intersection(hull(floor, arb(value.upper())))
    return Jet3(coefficients)


def physical_moment_parts(
    delta: arb, t: arb, s: Jet3, alpha: Jet3
) -> tuple[dict[str, list[Jet3]], list[Jet3]]:
    ds = [jet(delta), jet(1)] + [jet(0) for _ in range(PREC - 2)]
    beta = sinv(ds)
    beta_sqrt = ssqrt(beta)
    c, s4 = (t / 4).cos(), (t / 4).sin()
    p = jmul(jsin(jscale(s, arb(1) / 2)), jsin(jscale(s, arb(1) / 2)))
    q = jmul(
        jsin(jscale(alpha, arb(1) / 2)),
        jsin(jscale(alpha, arb(1) / 2)),
    )
    radius2 = jadd(
        jscale(jmul(jadd(1, jneg(p)), jadd(1, jneg(q))), 4 * c**2),
        jscale(jmul(p, q), 4 * s4**2),
    )
    radius = jsqrt(_apply_radius_floor(radius2))
    z = sscale(beta, jscale(radius, 2))
    a_scaled = _analytic_series(z, "A")
    b_scaled = _analytic_series(z, "B")
    dweight = jscale(jadd(1, jneg(jadd(p, q))), 2)
    cc = 2 * c**2 - 1
    cos_s, cos_a = jcos(s), jcos(alpha)
    fluctuation = jmul(
        jadd(cos_s, -1),
        jadd(
            jscale(jadd(jscale(cos_s, 2), 1), cc),
            jmul(cos_a, jadd(cos_s, 1 + cc)),
        ),
    )
    kernel = sscale(smul(smul(beta, beta), beta_sqrt), 2)
    kernel = smul(kernel, a_scaled)
    hkernel = smul(smul(beta, beta_sqrt), b_scaled)
    phase = sscale(beta, jadd(jscale(radius, 2), -4 * c))
    return {
        "KD": sscale(kernel, dweight),
        "KF": sscale(kernel, fluctuation),
        "HDD": sscale(hkernel, jmul(dweight, dweight)),
        "HDF": sscale(hkernel, jmul(dweight, fluctuation)),
    }, phase


def _calibrate(
    prefactors: dict[str, list[Jet3]], calibration: list[arb]
) -> dict[str, list[Jet3]]:
    gauge = [jet(value) for value in calibration]
    out = dict(prefactors)
    out["KF"] = sadd(out["KF"], sneg(smul(gauge, out["KD"])))
    out["HDF"] = sadd(out["HDF"], sneg(smul(gauge, out["HDD"])))
    return out


def _remove_constant_and_linear(phase: Jet3, gx: arb, gy: arb) -> Jet3:
    coefficients = dict(phase.coefficients)
    coefficients[0, 0] = arb(0)
    coefficients[1, 0] = phase.get(1, 0) - gx
    coefficients[0, 1] = phase.get(0, 1) - gy
    return Jet3(coefficients)


def centered_cell(
    delta: arb,
    t: arb,
    slo: arb,
    shi: arb,
    alo: arb,
    ahi: arb,
    calibration: list[arb],
) -> dict[str, list[arb]]:
    sm, am = (slo + shi) / 2, (alo + ahi) / 2
    rx, ry = (shi - slo) / 2, (ahi - alo) / 2
    center_pref, center_phase = physical_moment_parts(
        delta, t, variable_x(sm), variable_y(am)
    )
    box_pref, box_phase = physical_moment_parts(
        delta,
        t,
        variable_x(hull(slo, shi)),
        variable_y(hull(alo, ahi)),
    )
    center_pref = _calibrate(center_pref, calibration)
    box_pref = _calibrate(box_pref, calibration)
    center_correction = [jet(0)] + center_phase[1:]
    box_correction = [jet(0)] + box_phase[1:]
    center_values = {
        name: smul(value, sexp(center_correction))
        for name, value in center_pref.items()
    }
    box_values = {
        name: smul(value, sexp(box_correction))
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
    for name in NAMES:
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


def calibration_series(coefficients: tuple[arb, arb, arb]) -> list[arb]:
    return list(coefficients) + [arb(0) for _ in range(PREC - 3)]


def spatial_nodes(grid: int, power: int | Fraction = 1) -> list[arb]:
    power = power if isinstance(power, Fraction) else Fraction(power)
    if grid < 1 or power < 1 or power.denominator not in (1, 2):
        raise ValueError("grid and mesh power must be positive")
    nodes = []
    for index in range(grid + 1):
        ratio = arb(index) / grid
        value = ratio**power.numerator
        if power.denominator == 2:
            value = value.sqrt()
        nodes.append(arb("1.2") * value)
    if not all(nodes[index] < nodes[index + 1] for index in range(grid)):
        raise ValueError("spatial mesh is not strictly increasing")
    return nodes


def uniform_moments(
    delta: arb,
    t: arb,
    grid: int,
    calibration: list[arb],
    mesh_power: int | Fraction = 1,
) -> dict[str, list[arb]]:
    totals = {name: [arb(0) for _ in range(PREC)] for name in NAMES}
    nodes = spatial_nodes(grid, mesh_power)
    for i in range(grid):
        for j in range(grid):
            values = centered_cell(
                delta,
                t,
                nodes[i],
                nodes[i + 1],
                nodes[j],
                nodes[j + 1],
                calibration,
            )
            for name in NAMES:
                for order, value in enumerate(values[name]):
                    totals[name][order] += value
    return totals


def _wire_series(values: list[arb]) -> tuple[tuple[str, str], ...]:
    return tuple(_wire_arb(value) for value in values)


def _unwire_series(values: tuple[tuple[str, str], ...]) -> list[arb]:
    return [_unwire_arb(value) for value in values]


def _row_worker(arguments):
    (
        precision,
        delta_wire,
        t_wire,
        grid,
        row_start,
        row_stop,
        calibration_wire,
        mesh_power,
    ) = arguments
    ctx.prec = precision
    delta, t = _unwire_arb(delta_wire), _unwire_arb(t_wire)
    calibration = _unwire_series(calibration_wire)
    totals = {name: [arb(0) for _ in range(PREC)] for name in NAMES}
    nodes = spatial_nodes(grid, mesh_power)
    for i in range(row_start, row_stop):
        for j in range(grid):
            values = centered_cell(
                delta,
                t,
                nodes[i],
                nodes[i + 1],
                nodes[j],
                nodes[j + 1],
                calibration,
            )
            for name in NAMES:
                for order, value in enumerate(values[name]):
                    totals[name][order] += value
    return {name: _wire_series(values) for name, values in totals.items()}


def parallel_uniform_moments(
    delta: arb,
    t: arb,
    grid: int,
    calibration: list[arb],
    workers: int = 4,
    mesh_power: int | Fraction = 1,
) -> dict[str, list[arb]]:
    if workers < 1 or grid % workers:
        raise ValueError("grid must be divisible by the positive worker count")
    step = grid // workers
    arguments = [
        (
            ctx.prec,
            _wire_arb(delta),
            _wire_arb(t),
            grid,
            worker * step,
            (worker + 1) * step,
            _wire_series(calibration),
            mesh_power,
        )
        for worker in range(workers)
    ]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        pieces = list(executor.map(_row_worker, arguments))
    totals = {name: [arb(0) for _ in range(PREC)] for name in NAMES}
    for piece in pieces:
        for name in NAMES:
            for order, value in enumerate(_unwire_series(piece[name])):
                totals[name][order] += value
    return totals


def assemble_y(moments: dict[str, list[arb]], delta: arb) -> arb_series:
    series = {name: arb_series(values, PREC) for name, values in moments.items()}
    ds = arb_series([delta, arb(1)], PREC)
    numerator = series["KD"] * series["HDF"] - series["KF"] * series["HDD"]
    return 4 * numerator / (ds**4 * series["KD"]**2)


def centered_half_second_enclosure(
    delta_lo: arb,
    delta_hi: arb,
    t: arb,
    center_grid: int,
    remainder_grid: int,
    calibration_coefficients: tuple[arb, arb, arb],
    workers: int = 4,
    center_mesh_power: int | Fraction = 1,
    remainder_mesh_power: int | Fraction = 1,
) -> tuple[arb, arb_series, arb_series]:
    if not arb(0) < delta_lo <= delta_hi:
        raise ValueError("delta-eight S2 box must be positive and ordered")
    center, radius = (delta_lo + delta_hi) / 2, (delta_hi - delta_lo) / 2
    calibration = calibration_series(calibration_coefficients)
    def integrate(delta, t, grid, calibration, mesh_power):
        if workers == 1:
            return uniform_moments(
                delta, t, grid, calibration, mesh_power=mesh_power
            )
        return parallel_uniform_moments(
            delta,
            t,
            grid,
            calibration,
            workers=workers,
            mesh_power=mesh_power,
        )
    center_y = assemble_y(
        integrate(
            center, t, center_grid, calibration, center_mesh_power
        ),
        center,
    )
    box_y = assemble_y(
        integrate(
            hull(delta_lo, delta_hi),
            t,
            remainder_grid,
            calibration,
            remainder_mesh_power,
        ),
        hull(delta_lo, delta_hi),
    )
    center_coefficients = center_y.coeffs() + [arb(0)] * PREC
    box_coefficients = box_y.coeffs() + [arb(0)] * PREC
    perturbation = hull(-radius, radius)
    retained = arb(0)
    for order in reversed(range(2, 8)):
        retained = retained * perturbation
        retained += (
            arb(order * (order - 1)) * center_coefficients[order] / 2
        )
    remainder = (
        arb(28)
        * arb(box_coefficients[8].abs_upper())
        * radius**6
    )
    enclosure = retained + remainder * arb("0 +/- 1")
    return enclosure, center_y, box_y


def check() -> None:
    assert len(scaled_bessel_derivatives(arb("30 +/- 1"), "A", 13)) == 14
    print("S2 exact delta-eight/spatial-five infrastructure OK; no promotion")


if __name__ == "__main__":
    check()
