"""Exhaustive design cover for the regular delta<=0.007 candidate.

This driver is deliberately incapable of printing a certificate verdict.
Production requires a byte-separate provenance driver and validator after a
green run over all 158 immutable born t-boxes.
"""

import argparse

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_007_probe as probe


GRID_LADDER = (96, 192, 384)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--stop-index", type=int)
    args = parser.parse_args()
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    stop = len(boxes) if args.stop_index is None else args.stop_index
    if not 0 <= args.start_index < stop <= len(boxes):
        parser.error("invalid half-open design segment")
    histogram = {grid: 0 for grid in GRID_LADDER}
    worst = None
    print("R4 007 COVER DESIGN", "boxes", len(boxes),
          "segment", args.start_index, stop,
          "core_boxes", probe.CORE_BOXES,
          "annulus_boxes", probe.ANNULUS_BOXES,
          "physical_inner", probe.PHYSICAL_INNER,
          "grid_ladder", GRID_LADDER, flush=True)
    for index in range(args.start_index, stop):
        lo, hi = boxes[index]
        passed = None
        for grid in GRID_LADDER:
            try:
                radius, c4, value, margin = probe.judge(lo, hi, grid)
            except (ValueError, ZeroDivisionError) as exc:
                print("TRY", index, grid, "UNRESOLVED", type(exc).__name__,
                      str(exc), flush=True)
                continue
            lower = arb(margin.lower())
            print("TRY", index, "t", lo, hi, "grid", grid,
                  "radius", radius, "Y4", c4, "C_value", value,
                  "margin_lower", lower, flush=True)
            if lower > 0:
                passed = (grid, lower)
                break
        if passed is None:
            print("R4 007 COVER DESIGN FAIL", index, flush=True)
            return 1
        histogram[passed[0]] += 1
        if worst is None or passed[1] < worst[0]:
            worst = (passed[1], index)
        print("ROW DESIGN PASS", index, "grid", passed[0],
              "margin_lower", passed[1], flush=True)
    print("R4 007 COVER DESIGN SEGMENT PASS", args.start_index, stop,
          "rows", stop-args.start_index, "histogram", histogram,
          "worst_index", worst[1], "worst_margin_lower", worst[0],
          "PRODUCTION REQUIRED", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
