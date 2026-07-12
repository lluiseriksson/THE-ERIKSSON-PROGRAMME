"""Non-manifested partition-design helper for delta-box K4 trials."""

from __future__ import annotations

from flint import arb, ctx

from surface_remainder_complement import R_PHYSICAL
from surface_remainder_complement_l3_smoke import NAMES, centered_cell, nodes


def delta_box_coefficients(grid: int, delta: arb) -> dict[str, arb]:
    ctx.prec = 100
    t = arb("2.9")
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
