"""Adaptive fixed-domain smoke for the centred-delta K4 successor.

The ordinary second derivative is retained at the delta midpoint, while its
delta variation is charged with rigorous third/fourth derivative tracks.
Cells crossing a cutoff junction, or leaving the current z>=20 companion
contract, fall back to the earlier rigorous whole-delta enclosure.  This is
design code until a frozen delta partition and literal weighted sums pass.
"""

import heapq

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_complement import R_PHYSICAL
from surface_remainder_complement_l3_smoke import NAMES, centered_cell, nodes
from surface_remainder_centered_delta_carrier import centered_delta_cell


BUDGETS = {
    "MD_mirror": arb("56.801"),
    "MF_mirror": arb("156.28"),
    "MD2r_mirror": arb("12.577"),
    "MDFr_mirror": arb("44.352"),
    "muF_main": arb("26.467"),
    "nuD_main": arb("0.94119"),
    "nuF_main": arb("8.1751"),
}
DELTA_FINAL = arb(1)/15


def taylor_weight(lo, hi, endpoint=DELTA_FINAL):
    return endpoint*(hi-lo)-(hi**2-lo**2)/2


def single_box_fractions(totals, lo, hi):
    """Literal S1''' fractions for totals storing half of f''."""
    weight = taylor_weight(lo, hi)
    return {
        name: 2*arb(value.abs_upper())*weight/(BUDGETS[name]*DELTA_FINAL**2)
        for name, value in totals.items()
    }


def fractions_pass(fractions):
    """Literal local K4 verdict; every fraction must be finite and below 1."""
    return all(value.is_finite() and value.upper() < 1
               for value in fractions.values())


def evaluate_cell(delta_lo, delta_hi, t, slo, shi, alo, ahi):
    inside = bool(shi <= R_PHYSICAL) and bool(ahi <= R_PHYSICAL)
    try:
        values = centered_delta_cell(
            delta_lo, delta_hi, t, slo, shi, alo, ahi, inside)
        # A successful call is not enough: an interval operation can return
        # a non-finite ball when a carrier crosses the current companion
        # domain without raising.  Treat that cell exactly like an explicit
        # domain failure and use the registered whole-box fallback.
        if all(values[name].is_finite() for name in NAMES):
            return values, False
    except (ValueError, ZeroDivisionError):
        pass
    values = centered_cell(
        hull(delta_lo, delta_hi), t, slo, shi, alo, ahi, inside)
    if any(not values[name].is_finite() for name in NAMES):
        raise ValueError("centred K4 fallback returned a non-finite cell")
    return values, True


def adaptive_integral(delta_lo, delta_hi, t=arb("2.9"),
                      seed_grid=12, max_cells=576):
    if max_cells < (2*seed_grid)**2:
        raise ValueError("max_cells is smaller than the born partition")
    # ``nodes(seed_grid)`` already yields ``2*seed_grid`` intervals in each
    # coordinate (the physical-square and outer-annulus halves).  Thus the
    # registered seed ``12`` is the 24-by-24 = 576-cell born cover.
    partition = nodes(seed_grid)
    heap = []
    serial = 0

    def push(slo, shi, alo, ahi):
        nonlocal serial
        values, fallback = evaluate_cell(
            delta_lo, delta_hi, t, slo, shi, alo, ahi)
        # Non-finite interval cells are an admissibility failure, not a
        # low-priority numerical observation.  The previous ``nan`` score
        # could leave such a cell in the heap while finite but larger cells
        # were refined, so the 576-cell smoke accumulated ``nan`` totals.
        # Give every non-finite cell an explicit infinite priority; the
        # deterministic refinement ladder then removes it before any budget
        # score is compared.
        if any(not values[name].is_finite() for name in NAMES):
            score = float("inf")
        else:
            score = max(float(values[name].rad())/float(BUDGETS[name])
                        for name in NAMES)
        heapq.heappush(
            heap, (-score, serial, slo, shi, alo, ahi, values, fallback))
        serial += 1

    for i in range(len(partition)-1):
        for j in range(len(partition)-1):
            push(partition[i], partition[i+1],
                 partition[j], partition[j+1])
    while len(heap)+3 <= max_cells:
        _, _, slo, shi, alo, ahi, _, _ = heapq.heappop(heap)
        sm, am = (slo+shi)/2, (alo+ahi)/2
        push(slo, sm, alo, am)
        push(sm, shi, alo, am)
        push(slo, sm, am, ahi)
        push(sm, shi, am, ahi)
    totals = {name: arb(0) for name in NAMES}
    fallbacks = 0
    for *_, values, fallback in heap:
        fallbacks += int(fallback)
        for name in NAMES:
            totals[name] += values[name]
    return totals, len(heap), fallbacks


def main():
    ctx.prec = 140
    lo, hi = arb("0.049"), arb("0.05")
    for cells in (576, 1152):
        totals, count, fallbacks = adaptive_integral(
            lo, hi, max_cells=cells)
        assert all(value.is_finite() for value in totals.values())
        fractions = single_box_fractions(totals, lo, hi)
        print("CENTERED K4 DELTA DESIGN", "cells", count,
              "fallbacks", fallbacks,
              {name: value.str(8) for name, value in totals.items()},
              "fractions", {name: value.str(8)
                            for name, value in fractions.items()},
              flush=True)
    print("CENTERED K4 DELTA DESIGN FINITE; WEIGHTED COVER REQUIRED")


if __name__ == "__main__":
    main()
