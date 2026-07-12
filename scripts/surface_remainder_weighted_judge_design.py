"""Executable scaffold for the literal S1''' weighted remainder judge.

Design helper only until every delta box and the analytic K2 patch are present.
All stored carrier coefficients are one half of the second delta derivative.
"""

from __future__ import annotations

import heapq

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_complement import R_PHYSICAL
from surface_remainder_complement_l3_smoke import NAMES, centered_cell, nodes
from surface_remainder_core_l2_arb import localized_cell_bounds
from surface_remainder_delta_box_design import delta_box_coefficients


BUDGETS = {
    "MD_mirror": arb("56.801"),
    "MF_mirror": arb("156.28"),
    "MD2r_mirror": arb("12.577"),
    "MDFr_mirror": arb("44.352"),
    "muF_main": arb("26.467"),
    "nuD_main": arb("0.94119"),
    "nuF_main": arb("8.1751"),
}
DELTA_FINAL = arb(1) / 15


def taylor_weight(lo: arb, hi: arb, endpoint: arb = DELTA_FINAL) -> arb:
    return endpoint * (hi - lo) - (hi**2 - lo**2) / 2


def core_box_coefficients(grid: int, delta: arb) -> dict[str, arb]:
    """Localized-core c2 enclosures for all seven carriers on a delta box."""

    ctx.prec = 100
    t, length = arb("2.9"), arb(10)
    totals = {name: arb(0) for name in NAMES}
    for mirror in (False, True):
        active = NAMES[3:] if mirror else NAMES[:3]
        for i in range(grid):
            for j in range(grid):
                cell = localized_cell_bounds(
                    delta,
                    t,
                    length * i / grid,
                    length * (i + 1) / grid,
                    length * j / grid,
                    length * (j + 1) / grid,
                    mirror=mirror,
                )
                for name in active:
                    totals[name] += 4 * cell[name]
    return totals


def full_second_bounds(
    lo: arb, hi: arb, core_grid: int = 16, complement_grid: int = 12
) -> dict[str, arb]:
    delta = hull(lo, hi)
    core = core_box_coefficients(core_grid, delta)
    complement = delta_box_coefficients(complement_grid, delta)
    return {
        name: 2 * arb((core[name] + complement[name]).abs_upper())
        for name in NAMES
    }


def _adaptive_integral(seed_cells, evaluator, max_cells: int) -> dict[str, arb]:
    heap = []
    serial = 0

    def push(slo, shi, alo, ahi) -> None:
        nonlocal serial
        values = evaluator(slo, shi, alo, ahi)
        score = max(
            float(values[name].rad()) / float(BUDGETS[name]) for name in NAMES
        )
        heapq.heappush(
            heap, (-score, serial, slo, shi, alo, ahi, values)
        )
        serial += 1

    for cell in seed_cells:
        push(*cell)
    while len(heap) + 3 <= max_cells:
        _, _, slo, shi, alo, ahi, _ = heapq.heappop(heap)
        sm, am = (slo + shi) / 2, (alo + ahi) / 2
        push(slo, sm, alo, am)
        push(sm, shi, alo, am)
        push(slo, sm, am, ahi)
        push(sm, shi, am, ahi)
    totals = {name: arb(0) for name in NAMES}
    for *_, values in heap:
        for name in NAMES:
            totals[name] += values[name]
    return totals


def adaptive_core_box(delta: arb, max_cells: int = 1024) -> dict[str, arb]:
    t, length, seed = arb("2.9"), arb(10), 4
    seeds = [
        (length * i / seed, length * (i + 1) / seed,
         length * j / seed, length * (j + 1) / seed)
        for i in range(seed) for j in range(seed)
    ]

    def evaluate(slo, shi, alo, ahi):
        out = {name: arb(0) for name in NAMES}
        for mirror, active in ((False, NAMES[:3]), (True, NAMES[3:])):
            values = localized_cell_bounds(
                delta, t, slo, shi, alo, ahi, mirror=mirror
            )
            for name in active:
                out[name] = 4 * values[name]
        return out

    return _adaptive_integral(seeds, evaluate, max_cells)


def adaptive_complement_box(delta: arb, max_cells: int = 1024) -> dict[str, arb]:
    partition = nodes(4)
    seeds = [
        (partition[i], partition[i + 1], partition[j], partition[j + 1])
        for i in range(len(partition) - 1)
        for j in range(len(partition) - 1)
    ]

    def evaluate(slo, shi, alo, ahi):
        inside = bool(shi <= R_PHYSICAL) and bool(ahi <= R_PHYSICAL)
        return centered_cell(delta, arb("2.9"), slo, shi, alo, ahi, inside)

    return _adaptive_integral(seeds, evaluate, max_cells)


def adaptive_full_second_bounds(
    lo: arb, hi: arb, core_cells: int = 1024, complement_cells: int = 1024
) -> dict[str, arb]:
    delta = hull(lo, hi)
    core = adaptive_core_box(delta, core_cells)
    complement = adaptive_complement_box(delta, complement_cells)
    return {
        name: 2 * arb((core[name] + complement[name]).abs_upper())
        for name in NAMES
    }


def judge_rows(
    partition: list[arb], bounds: list[dict[str, arb]]
) -> dict[str, tuple[arb, arb, bool]]:
    if len(partition) != len(bounds) + 1:
        raise ValueError("one bound dictionary is required per partition box")
    sums = {name: arb(0) for name in NAMES}
    for lo, hi, row in zip(partition, partition[1:], bounds):
        weight = taylor_weight(lo, hi)
        for name in NAMES:
            sums[name] += row[name] * weight
    return {
        name: (value, BUDGETS[name] * DELTA_FINAL**2,
               bool(value <= BUDGETS[name] * DELTA_FINAL**2))
        for name, value in sums.items()
    }


def check() -> None:
    assert taylor_weight(arb(0), DELTA_FINAL).overlaps(DELTA_FINAL**2 / 2)
    assert all(value > 0 for value in BUDGETS.values())
    print("S1''' weighted-judge scaffold OK; coverage and K2 remain open")


if __name__ == "__main__":
    check()
