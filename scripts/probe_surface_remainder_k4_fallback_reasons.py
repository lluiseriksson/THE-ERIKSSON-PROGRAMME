"""Design-only classification of K4 centred-delta fallback cells.

This deliberately duplicates the adaptive partition ladder without changing
the production integrator.  It records the exception that sends a cell from
``centered_delta_cell`` to the junction-safe ``centered_cell`` fallback.
No output from this probe is a K4 or G6 certificate.
"""

import argparse
import heapq
from collections import Counter

from flint import arb, ctx

import surface_remainder_centered_delta_integrator_design as design
from surface_remainder_arb_jet2 import hull
from surface_remainder_complement import R_PHYSICAL
from surface_remainder_complement_l3_smoke import NAMES, nodes, centered_cell
from surface_remainder_centered_delta_carrier import centered_delta_cell


def classify(delta_lo, delta_hi, t, seed_grid=12, max_cells=1152):
    partition = nodes(seed_grid)
    heap = []
    serial = 0

    def evaluate(slo, shi, alo, ahi):
        inside = bool(shi <= R_PHYSICAL) and bool(ahi <= R_PHYSICAL)
        reason = "none"
        try:
            values = centered_delta_cell(
                delta_lo, delta_hi, t, slo, shi, alo, ahi, inside)
            if not all(values[name].is_finite() for name in NAMES):
                reason = "nonfinite-centred"
                raise ValueError(reason)
            return values, False, reason
        except Exception as exc:  # design probe: retain exact reason text
            reason = f"{type(exc).__name__}: {exc}"
            values = centered_cell(
                hull(delta_lo, delta_hi), t, slo, shi, alo, ahi, inside)
            return values, True, reason

    def push(slo, shi, alo, ahi):
        nonlocal serial
        values, fallback, reason = evaluate(slo, shi, alo, ahi)
        score = max(float(values[name].rad()) / float(design.BUDGETS[name])
                    for name in NAMES)
        heapq.heappush(
            heap, (-score, serial, slo, shi, alo, ahi, values, fallback,
                   reason))
        serial += 1

    for i in range(len(partition) - 1):
        for j in range(len(partition) - 1):
            push(partition[i], partition[i + 1], partition[j], partition[j + 1])
    while len(heap) + 3 <= max_cells:
        _, _, slo, shi, alo, ahi, _, _, _ = heapq.heappop(heap)
        sm, am = (slo + shi) / 2, (alo + ahi) / 2
        push(slo, sm, alo, am)
        push(sm, shi, alo, am)
        push(slo, sm, am, ahi)
        push(sm, shi, am, ahi)

    reasons = Counter(item[-1] for item in heap if item[-2])
    fallback_items = [item for item in heap if item[-2]]
    print(f"K4 FALLBACK REASONS t={t} delta=[{delta_lo},{delta_hi}] "
          f"cells={len(heap)} fallback={len(fallback_items)}")
    for reason, count in reasons.most_common():
        print(f"reason {count} {reason}")
    for item in fallback_items[:20]:
        _, _, slo, shi, alo, ahi, values, _, reason = item
        print("cell", slo, shi, alo, ahi, reason,
              {name: values[name].str(6) for name in NAMES})


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--delta-lo", default="0.049")
    parser.add_argument("--delta-hi", default="0.05")
    parser.add_argument("--t", default="2.97125")
    parser.add_argument("--max-cells", type=int, default=1152)
    args = parser.parse_args()
    ctx.prec = 140
    classify(arb(args.delta_lo), arb(args.delta_hi), arb(args.t),
             max_cells=args.max_cells)

