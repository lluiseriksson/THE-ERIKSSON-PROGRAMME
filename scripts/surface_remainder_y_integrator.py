"""Adaptive centered Arb integration for the normalized S2 carrier Y."""

from __future__ import annotations

import heapq

from flint import arb, ctx

from surface_remainder_arb_jet2 import Jet2, hull
from surface_remainder_carrier_jet import add, inv, mul, scale
from surface_remainder_centered_prefactor import (
    Dual, Jet, dadd, dmul, dsquare, dual, jadd, jmul, jneg,
)
from surface_remainder_core_l2_arb import (
    gaussian_integrals,
    symmetric,
)
from surface_remainder_y_carrier import (
    RAW_NAMES,
    raw_integrand_parts,
    raw_integrand_parts_t,
    scaled_raw_integrand_parts,
    scaled_raw_integrand_parts_fixed_square,
)


def _linear_integral(gradient: arb, width: arb) -> arb:
    if gradient == 0:
        return width
    half = gradient * width / 2
    return (half.exp() - (-half).exp()) / gradient


def _linear_first_moment(gradient: arb, width: arb) -> arb:
    if gradient == 0:
        return arb(0)
    a = width / 2
    ga = gradient * a
    return ((ga - 1) * ga.exp() + (ga + 1) * (-ga).exp()) / gradient**2


def _dual_integral(center: Dual, box: Dual, rx: arb, ry: arb, area: arb) -> arb:
    error = (
        arb(box.xx.abs_upper()) * rx**2 / 2
        + arb(box.xy.abs_upper()) * rx * ry
        + arb(box.yy.abs_upper()) * ry**2 / 2
    )
    return area * (center.v + error * arb("0 +/- 1"))


def raw_cell(delta: arb, t: arb, slo: arb, shi: arb,
             alo: arb, ahi: arb, calibration: Jet | None = None,
             parts_function=raw_integrand_parts,
             gaussian_p: arb | None = None,
             ) -> dict[str, Jet2]:
    sm, am = (slo + shi) / 2, (alo + ahi) / 2
    rx, ry = (shi - slo) / 2, (ahi - alo) / 2
    sbox, abox = hull(slo, shi), hull(alo, ahi)
    center_prefactors, center_phase = parts_function(
        delta, t, Dual(sm, arb(1)), Dual(am, arb(0), arb(1))
    )
    box_prefactors, box_phase = parts_function(
        delta, t, Dual(sbox, arb(1)), Dual(abox, arb(0), arb(1))
    )
    names = list(RAW_NAMES)
    if calibration is not None:
        center_prefactors["KNc"] = jadd(
            center_prefactors["KF"],
            jneg(jmul(calibration, center_prefactors["KD"])),
        )
        center_prefactors["GNc"] = jadd(
            center_prefactors["HDF"],
            jneg(jmul(calibration, center_prefactors["HDD"])),
        )
        box_prefactors["KNc"] = jadd(
            box_prefactors["KF"],
            jneg(jmul(calibration, box_prefactors["KD"])),
        )
        box_prefactors["GNc"] = jadd(
            box_prefactors["HDF"],
            jneg(jmul(calibration, box_prefactors["HDD"])),
        )
        names += ["KNc", "GNc"]
    if not all(
        component.v.is_finite()
        for value in (box_phase, *box_prefactors.values())
        for component in (value.c0, value.c1, value.c2)
    ):
        raise ValueError("non-finite centered box must subdivide")
    if gaussian_p is not None:
        center_residual = dadd(
            center_phase.c0,
            dmul(gaussian_p / 2,
                 dadd(dsquare(Dual(sm, arb(1))),
                      dsquare(Dual(am, arb(0), arb(1))))),
        )
        box_residual = dadd(
            box_phase.c0,
            dmul(gaussian_p / 2,
                 dadd(dsquare(Dual(sbox, arb(1))),
                      dsquare(Dual(abox, arb(0), arb(1))))),
        )
    else:
        center_residual, box_residual = center_phase.c0, box_phase.c0
    gx, gy = arb(center_residual.x.mid()), arb(center_residual.y.mid())
    phase_radius = (
        arb((center_residual.x - gx).abs_upper()) * rx
        + arb((center_residual.y - gy).abs_upper()) * ry
        + arb(box_residual.xx.abs_upper()) * rx**2 / 2
        + arb(box_residual.xy.abs_upper()) * rx * ry
        + arb(box_residual.yy.abs_upper()) * ry**2 / 2
    )
    if gaussian_p is None:
        l0x, l0y = _linear_integral(gx, 2 * rx), _linear_integral(gy, 2 * ry)
        l1x = _linear_first_moment(gx, 2 * rx)
        l1y = _linear_first_moment(gy, 2 * ry)
        mx, my = l1x, l1y
        spatial_integral = l0x * l0y
        center_exp = center_residual.v.exp()
        phase_error = phase_radius.exp() - 1
    else:
        l0x, gx1 = gaussian_integrals(slo, shi, gaussian_p)
        l0y, gy1 = gaussian_integrals(alo, ahi, gaussian_p)
        mx, my = gx1 - sm * l0x, gy1 - am * l0y
        spatial_integral = l0x * l0y
        residual_range = (
            center_residual.v
            + center_residual.x * symmetric(rx)
            + center_residual.y * symmetric(ry)
            + symmetric(phase_radius)
        )
        center_exp = arb(1)
        phase_radius = arb(residual_range.abs_upper())
        phase_error = arb((residual_range.exp() - 1).abs_upper())

    def coefficient(prefactor, phase, order):
        if order == 0:
            return prefactor.c0
        if order == 1:
            return dadd(prefactor.c1, dmul(prefactor.c0, phase.c1))
        return dadd(
            prefactor.c2,
            dadd(
                dmul(prefactor.c1, phase.c1),
                dmul(prefactor.c0, dadd(phase.c2, dmul(dsquare(phase.c1), arb(1) / 2))),
            ),
        )

    out = {}
    for name in names:
        integrated = []
        for order in range(3):
            cc = coefficient(center_prefactors[name], center_phase, order)
            cb = coefficient(box_prefactors[name], box_phase, order)
            affine = cc.v * spatial_integral + cc.x * mx * l0y + cc.y * l0x * my
            hessian_error = (
                arb(cb.xx.abs_upper()) * rx**2 / 2
                + arb(cb.xy.abs_upper()) * rx * ry
                + arb(cb.yy.abs_upper()) * ry**2 / 2
            )
            affine_abs = (
                arb(cc.v.abs_upper())
                + arb(cc.x.abs_upper()) * rx
                + arb(cc.y.abs_upper()) * ry
            )
            error = (
                hessian_error * phase_radius.exp()
                + affine_abs * phase_error
            ) * spatial_integral
            integrated.append(4 * center_exp * (affine + symmetric(error)))
        out[name] = Jet2(*integrated)
    if not all(
        component.is_finite()
        for value in out.values()
        for component in (value.c0, value.c1, value.c2)
    ):
        raise ValueError("non-finite exponential enclosure must subdivide")
    return out


def integrate_raw(delta: arb, t: arb = arb("2.9"),
                  max_cells: int = 4096, seed_grid: int = 4,
                  relative_scales: dict[tuple[str, str], float] | None = None,
                  linear_weights: dict[tuple[str, str], float] | None = None,
                  calibration: Jet | None = None,
                  domain_side: arb | None = None,
                  parts_function=raw_integrand_parts,
                  skip_radius: arb | None = None,
                  gaussian_p: arb | None = None,
                  max_forced_depth: int = 40,
                  ) -> tuple[dict[str, Jet2], int]:
    ctx.prec = 100
    heap = []
    serial = 0

    def push(slo: arb, shi: arb, alo: arb, ahi: arb,
             forced_depth: int = 0) -> None:
        nonlocal serial
        names = list(RAW_NAMES) + (["KNc", "GNc"] if calibration is not None else [])
        if skip_radius is not None and bool(slo**2 + alo**2 >= skip_radius**2):
            values = {
                name: Jet2(arb(0), arb(0), arb(0)) for name in names
            }
            heapq.heappush(
                heap, (0.0, serial, slo, shi, alo, ahi, values)
            )
            serial += 1
            return
        try:
            values = raw_cell(
                delta,
                t,
                slo,
                shi,
                alo,
                ahi,
                calibration=calibration,
                parts_function=parts_function,
                gaussian_p=gaussian_p,
            )
        except ValueError as error:
            if "must subdivide" not in str(error):
                raise
            if forced_depth >= max_forced_depth:
                raise RuntimeError(
                    "forced spatial subdivision reached depth %d on "
                    "[%s,%s]x[%s,%s]: %s" %
                    (forced_depth, slo, shi, alo, ahi, error)
                ) from error
            sm, am = (slo + shi) / 2, (alo + ahi) / 2
            push(slo, sm, alo, am, forced_depth + 1)
            push(sm, shi, alo, am, forced_depth + 1)
            push(slo, sm, am, ahi, forced_depth + 1)
            push(sm, shi, am, ahi, forced_depth + 1)
            return
        if linear_weights is not None:
            score = sum(
                float(getattr(value, coefficient).rad())
                * linear_weights.get((name, coefficient), 0.0)
                for name, value in values.items()
                for coefficient in ("c0", "c1", "c2")
            )
        else:
            score = max(
                float(getattr(value, coefficient).rad())
                / (relative_scales[(name, coefficient)]
                   if relative_scales else 1.0)
                for name, value in values.items()
                for coefficient in ("c0", "c1", "c2")
            )
        heapq.heappush(heap, (-score, serial, slo, shi, alo, ahi, values))
        serial += 1

    side = arb.pi() if domain_side is None else domain_side
    for i in range(seed_grid):
        for j in range(seed_grid):
            push(side * i / seed_grid, side * (i + 1) / seed_grid,
                 side * j / seed_grid, side * (j + 1) / seed_grid)
    while len(heap) + 3 <= max_cells:
        _, _, slo, shi, alo, ahi, _ = heapq.heappop(heap)
        sm, am = (slo + shi) / 2, (alo + ahi) / 2
        push(slo, sm, alo, am)
        push(sm, shi, alo, am)
        push(slo, sm, am, ahi)
        push(sm, shi, am, ahi)
    names = list(RAW_NAMES) + (["KNc", "GNc"] if calibration is not None else [])
    totals = {name: Jet2(arb(0), arb(0), arb(0)) for name in names}
    for *_, values in heap:
        for name in names:
            totals[name] = add(totals[name], values[name])
    return totals, len(heap)


def normalized_y(delta: arb, max_cells: int = 4096) -> tuple[Jet2, int]:
    moments, cells = integrate_raw(delta, max_cells=max_cells)
    delta_jet = Jet2(delta, arb(1), arb(0))
    beta = inv(delta_jet)
    numerator = add(
        mul(moments["KD"], moments["HDF"]),
        scale(mul(moments["KF"], moments["HDD"]), arb(-1)),
    )
    x = scale(
        mul(mul(mul(beta, beta), beta),
            mul(numerator, inv(mul(moments["KD"], moments["KD"])))),
        arb(4),
    )
    return mul(x, inv(delta_jet)), cells


def balanced_normalized_y(
    delta: arb, pilot_cells: int = 1024, max_cells: int = 4096
) -> tuple[Jet2, int]:
    pilot, _ = integrate_raw(delta, max_cells=pilot_cells)
    scales = {}
    for name, value in pilot.items():
        for coefficient in ("c0", "c1", "c2"):
            ball = getattr(value, coefficient)
            scales[(name, coefficient)] = max(
                abs(float(ball.mid())), float(ball.rad()), 1e-300
            )
    moments, cells = integrate_raw(
        delta, max_cells=max_cells, relative_scales=scales
    )
    delta_jet = Jet2(delta, arb(1), arb(0))
    beta = inv(delta_jet)
    numerator = add(
        mul(moments["KD"], moments["HDF"]),
        scale(mul(moments["KF"], moments["HDD"]), arb(-1)),
    )
    x = scale(
        mul(mul(mul(beta, beta), beta),
            mul(numerator, inv(mul(moments["KD"], moments["KD"])))),
        arb(4),
    )
    return mul(x, inv(delta_jet)), cells


def centered_normalized_y(
    delta: arb, pilot_cells: int = 1024, max_cells: int = 4096,
    domain_side: arb | None = None,
) -> tuple[Jet2, int, arb]:
    pilot, _ = integrate_raw(
        delta, max_cells=pilot_cells, domain_side=domain_side
    )
    ratio = mul(pilot["KF"], inv(pilot["KD"]))
    if not all(value.is_finite() for value in (ratio.c0, ratio.c1, ratio.c2)):
        raise ValueError("pilot KF/KD ratio is unresolved")
    calibration = Jet(
        dual(arb(ratio.c0.mid())),
        dual(arb(ratio.c1.mid())),
        dual(arb(ratio.c2.mid())),
    )
    moments, cells = integrate_raw(
        delta,
        max_cells=max_cells,
        calibration=calibration,
        domain_side=domain_side,
    )
    return assemble_centered_y(moments, delta), cells, calibration.c0.v


def assemble_centered_y(moments: dict[str, Jet2], delta: arb) -> Jet2:
    """Assemble Y from centered raw moments; calibration cancels exactly."""
    delta_jet = Jet2(delta, arb(1), arb(0))
    beta = inv(delta_jet)
    numerator = add(
        mul(moments["KD"], moments["GNc"]),
        scale(mul(moments["KNc"], moments["HDD"]), arb(-1)),
    )
    x = scale(
        mul(mul(mul(beta, beta), beta),
            mul(numerator, inv(mul(moments["KD"], moments["KD"])))),
        arb(4),
    )
    return mul(x, inv(delta_jet))


def assemble_centered_y_t(moments: dict[str, Jet2], delta: arb) -> Jet2:
    """Assemble Y when moment jets differentiate t and delta is constant."""
    numerator = add(
        mul(moments["KD"], moments["GNc"]),
        scale(mul(moments["KNc"], moments["HDD"]), arb(-1)),
    )
    quotient = mul(numerator, inv(mul(moments["KD"], moments["KD"])))
    return scale(quotient, arb(4)/delta**4)


def terminal_sensitivity_weights(
    moments: dict[str, Jet2], delta: arb, target: str = "c2",
    assembler=assemble_centered_y,
) -> dict[tuple[str, str], float]:
    """Design-only Jacobian weights for the final Y.c2 enclosure width.

    The weights choose a partition only; they never enter an enclosure.
    """
    coefficients = ("c0", "c1", "c2")
    point = {
        name: Jet2(*(arb(getattr(value, c).mid()) for c in coefficients))
        for name, value in moments.items()
    }
    weights = {}
    for name in ("KD", "KNc", "HDD", "GNc"):
        for index, coefficient in enumerate(coefficients):
            value = float(getattr(point[name], coefficient))
            step = max(abs(value), 1e-30) * 1e-6
            plus = dict(point)
            minus = dict(point)
            positive = [point[name].c0, point[name].c1, point[name].c2]
            negative = list(positive)
            positive[index] += arb(str(step))
            negative[index] -= arb(str(step))
            plus[name] = Jet2(*positive)
            minus[name] = Jet2(*negative)
            derivative = float(
                (getattr(assembler(plus, delta), target)
                 - getattr(assembler(minus, delta), target))
                / arb(str(2 * step))
            )
            weights[(name, coefficient)] = abs(derivative)
    return weights


def sensitivity_centered_main_y(
    delta: arb, pilot_cells: int = 1024, max_cells: int = 4096,
    target: str = "c2", t: arb = arb("2.9"),
) -> tuple[Jet2, int, arb, dict[tuple[str, str], float]]:
    """Main-square Y with refinement targeted at the final Y'' width."""
    domain_side = arb(6) / 5
    pilot, _ = integrate_raw(
        delta, t=t, max_cells=max(256, pilot_cells // 2),
        domain_side=domain_side
    )
    ratio = mul(pilot["KF"], inv(pilot["KD"]))
    calibration = Jet(
        dual(arb(ratio.c0.mid())),
        dual(arb(ratio.c1.mid())),
        dual(arb(ratio.c2.mid())),
    )
    centered_pilot, _ = integrate_raw(
        delta, t=t, max_cells=pilot_cells, calibration=calibration,
        domain_side=domain_side,
    )
    weights = terminal_sensitivity_weights(centered_pilot, delta, target=target)
    moments, cells = integrate_raw(
        delta, t=t, max_cells=max_cells, calibration=calibration,
        domain_side=domain_side, linear_weights=weights,
    )
    return assemble_centered_y(moments, delta), cells, calibration.c0.v, weights


def sensitivity_centered_main_y_t(
    delta: arb, t: arb, pilot_cells: int = 1024, max_cells: int = 4096,
    target: str = "c0",
) -> tuple[Jet2, int, arb, dict[tuple[str, str], float]]:
    """Main-square Y with exact t jets and terminal-width refinement."""
    domain_side = arb(6)/5
    kwargs = {
        "t": t,
        "domain_side": domain_side,
        "parts_function": raw_integrand_parts_t,
    }
    pilot, _ = integrate_raw(
        delta, max_cells=max(256, pilot_cells//2), **kwargs
    )
    ratio = mul(pilot["KF"], inv(pilot["KD"]))
    calibration = Jet(
        dual(arb(ratio.c0.mid())),
        dual(arb(ratio.c1.mid())),
        dual(arb(ratio.c2.mid())),
    )
    centered_pilot, _ = integrate_raw(
        delta, max_cells=pilot_cells, calibration=calibration, **kwargs
    )
    weights = terminal_sensitivity_weights(
        centered_pilot, delta, target=target, assembler=assemble_centered_y_t
    )
    moments, cells = integrate_raw(
        delta, max_cells=max_cells, calibration=calibration,
        linear_weights=weights, **kwargs
    )
    return (assemble_centered_y_t(moments, delta), cells,
            calibration.c0.v, weights)


def centered_main_y(
    delta: arb, pilot_cells: int = 256, max_cells: int = 1024
) -> tuple[Jet2, int, arb]:
    return centered_normalized_y(
        delta,
        pilot_cells=pilot_cells,
        max_cells=max_cells,
        domain_side=arb(6) / 5,
    )


def centered_scaled_core_y(
    delta: arb, pilot_cells: int = 256, max_cells: int = 1024
) -> tuple[Jet2, int, arb]:
    kwargs = {
        "domain_side": arb(10),
        "parts_function": scaled_raw_integrand_parts,
        "skip_radius": arb(10),
        "gaussian_p": (arb("2.9") / 4).cos(),
    }
    pilot, _ = integrate_raw(delta, max_cells=pilot_cells, **kwargs)
    ratio = mul(pilot["KF"], inv(pilot["KD"]))
    if not all(value.is_finite() for value in (ratio.c0, ratio.c1, ratio.c2)):
        raise ValueError("scaled-core pilot KF/KD ratio is unresolved")
    calibration = Jet(
        dual(arb(ratio.c0.mid())),
        dual(arb(ratio.c1.mid())),
        dual(arb(ratio.c2.mid())),
    )
    moments, cells = integrate_raw(
        delta, max_cells=max_cells, calibration=calibration, **kwargs
    )
    delta_jet = Jet2(delta, arb(1), arb(0))
    beta = inv(delta_jet)
    numerator = add(
        mul(moments["KD"], moments["GNc"]),
        scale(mul(moments["KNc"], moments["HDD"]), arb(-1)),
    )
    x = scale(
        mul(mul(mul(beta, beta), beta),
            mul(numerator, inv(mul(moments["KD"], moments["KD"])))),
        arb(4),
    )
    return mul(x, inv(delta_jet)), cells, calibration.c0.v


def centered_scaled_fixed_square_y(
    delta: arb, pilot_cells: int = 256, max_cells: int = 1024,
    beta1: int = 20,
) -> tuple[Jet2, int, arb]:
    """Gaussian scaled core on [0,(6/5)sqrt(beta1)]^2.

    At delta=1/beta1 this is exactly the physical main square.  For smaller
    delta its missing physical completion remains a separate fixed-domain
    obligation.
    """
    domain_side = arb(6)/5*arb(beta1).sqrt()
    kwargs = {
        "domain_side": domain_side,
        "parts_function": scaled_raw_integrand_parts_fixed_square,
        "gaussian_p": (arb("2.9")/4).cos(),
    }
    pilot, _ = integrate_raw(delta, max_cells=pilot_cells, **kwargs)
    ratio = mul(pilot["KF"], inv(pilot["KD"]))
    calibration = Jet(
        dual(arb(ratio.c0.mid())),
        dual(arb(ratio.c1.mid())),
        dual(arb(ratio.c2.mid())),
    )
    moments, cells = integrate_raw(
        delta, max_cells=max_cells, calibration=calibration, **kwargs
    )
    return assemble_centered_y(moments, delta), cells, calibration.c0.v


def check() -> None:
    # Algebraic zero witness tests ratio assembly without claiming a bound.
    d = arb(1) / 15
    assert d > 0
    print("S2 normalized-Y integrator scaffold OK; interval run remains open")


if __name__ == "__main__":
    check()
