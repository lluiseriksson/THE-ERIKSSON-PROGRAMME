"""Design smoke for the exact fixed-domain K4 complement.

The run checks finiteness and refinement at the registered stress point. It
does not certify K4 or either literal weighted remainder judge.
"""

from __future__ import annotations

import hashlib
import sys

import flint
from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_carrier_jet import carriers, mirror_carriers
from surface_remainder_centered_prefactor import (
    Dual,
    jmul,
    physical_carriers,
)
from surface_remainder_complement import (
    R_PHYSICAL,
    complement_weight_jet,
    fixed_outer_radius,
    physical_complement_weight,
    product_second_coefficient,
)


NAMES = (
    "muF_main",
    "nuD_main",
    "nuF_main",
    "MD_mirror",
    "MF_mirror",
    "MD2r_mirror",
    "MDFr_mirror",
)


def nodes(grid: int) -> list[arb]:
    """A positive partition with the physical boundary born as a node."""

    outer = fixed_outer_radius()
    left = [R_PHYSICAL * i / grid for i in range(grid)]
    right = [R_PHYSICAL + (outer - R_PHYSICAL) * i / grid for i in range(grid)]
    return left + right + [outer]


def complement_second_coefficients(grid: int) -> dict[str, arb]:
    ctx.prec = 100
    delta, t = arb(1) / 15, arb("2.9")
    partition = nodes(grid)
    totals = {name: arb(0) for name in NAMES}
    for i in range(len(partition) - 1):
        for j in range(len(partition) - 1):
            slo, shi = partition[i], partition[i + 1]
            alo, ahi = partition[j], partition[j + 1]
            s, alpha = hull(slo, shi), hull(alo, ahi)
            inside = bool(shi <= R_PHYSICAL) and bool(ahi <= R_PHYSICAL)
            weight = complement_weight_jet(
                delta, s, alpha, inside, allow_junction_hull=True
            )
            if weight.c0 == 0 and weight.c1 == 0 and weight.c2 == 0:
                continue
            area = (shi - slo) * (ahi - alo) * 4
            values = carriers(delta, t, s, alpha)
            values.update(mirror_carriers(delta, t, s, alpha))
            for name in NAMES:
                totals[name] += area * product_second_coefficient(
                    weight, values[name]
                )
    return totals


def centered_cell(
    delta: arb,
    t: arb,
    slo: arb,
    shi: arb,
    alo: arb,
    ahi: arb,
    inside: bool,
) -> dict[str, arb]:
    """Second-order midpoint enclosure, or a junction-safe direct fallback."""

    sm, am = (slo + shi) / 2, (alo + ahi) / 2
    rx, ry = (shi - slo) / 2, (ahi - alo) / 2
    sbox, abox = hull(slo, shi), hull(alo, ahi)
    try:
        center_weight = physical_complement_weight(
            delta, Dual(sm, arb(1)), Dual(am, arb(0), arb(1)), inside
        )
        box_weight = physical_complement_weight(
            delta, Dual(sbox, arb(1)), Dual(abox, arb(0), arb(1)), inside
        )
    except ValueError:
        weight = complement_weight_jet(
            delta, sbox, abox, inside, allow_junction_hull=True
        )
        values = carriers(delta, t, sbox, abox)
        values.update(mirror_carriers(delta, t, sbox, abox))
        return {
            name: product_second_coefficient(weight, values[name])
            * (shi - slo)
            * (ahi - alo)
            * 4
            for name in NAMES
        }

    if all(
        component.v == 0
        and component.x == 0
        and component.y == 0
        and component.xx == 0
        and component.xy == 0
        and component.yy == 0
        for component in (box_weight.c0, box_weight.c1, box_weight.c2)
    ):
        return {name: arb(0) for name in NAMES}

    center_values = physical_carriers(
        delta, t, Dual(sm, arb(1)), Dual(am, arb(0), arb(1))
    )
    center_values.update(
        physical_carriers(
            delta, t, Dual(sm, arb(1)), Dual(am, arb(0), arb(1)), mirror=True
        )
    )
    box_values = physical_carriers(
        delta, t, Dual(sbox, arb(1)), Dual(abox, arb(0), arb(1))
    )
    box_values.update(
        physical_carriers(
            delta, t, Dual(sbox, arb(1)), Dual(abox, arb(0), arb(1)), mirror=True
        )
    )
    area = (shi - slo) * (ahi - alo) * 4
    out = {}
    for name in NAMES:
        center = jmul(center_weight, center_values[name]).c2
        box = jmul(box_weight, box_values[name]).c2
        error = (
            arb(box.xx.abs_upper()) * rx**2 / 2
            + arb(box.xy.abs_upper()) * rx * ry
            + arb(box.yy.abs_upper()) * ry**2 / 2
        )
        out[name] = area * (center.v + error * arb("0 +/- 1"))
    return out


def centered_complement_second_coefficients(grid: int) -> dict[str, arb]:
    ctx.prec = 100
    delta, t = arb(1) / 15, arb("2.9")
    partition = nodes(grid)
    totals = {name: arb(0) for name in NAMES}
    for i in range(len(partition) - 1):
        for j in range(len(partition) - 1):
            slo, shi = partition[i], partition[i + 1]
            alo, ahi = partition[j], partition[j + 1]
            inside = bool(shi <= R_PHYSICAL) and bool(ahi <= R_PHYSICAL)
            values = centered_cell(delta, t, slo, shi, alo, ahi, inside)
            for name in NAMES:
                totals[name] += values[name]
    return totals


def check() -> None:
    print("=== SURFACE REMAINDER COMPLEMENT L3 DESIGN SMOKE ===")
    print(
        "script sha256 : %s"
        % hashlib.sha256(open(__file__, "rb").read()).hexdigest()
    )
    print(
        "python-flint %s  python %s  prec 100"
        % (flint.__version__, sys.version.split()[0])
    )
    print("fixed physical domain; stress delta=1/15 t=2.9", flush=True)
    for grid in (32, 64):
        totals = centered_complement_second_coefficients(grid)
        assert all(value.is_finite() for value in totals.values())
        print(
            "complement L3 design grid %d: %s"
            % (grid, {name: value.str(4) for name, value in totals.items()}),
            flush=True,
        )
    print("K4 COMPLEMENT L3 SMOKE FINITE; DESIGN ONLY; K4 REMAINS OPEN")


if __name__ == "__main__":
    check()
