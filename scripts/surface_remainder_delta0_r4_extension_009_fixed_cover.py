"""Frozen-map exhaustive design cover for the delta<=0.009 candidate."""

import argparse

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_009_cover as cover


GRID_RANGES = ((0, 49, 384), (50, 145, 192), (146, 157, 384))
SEGMENTS = ((0, 13), (13, 25), (25, 38), (38, 50),
            (50, 98), (98, 146), (146, 152), (152, 158))


def grid_for(index):
    matches = [grid for lo, hi, grid in GRID_RANGES if lo <= index <= hi]
    if len(matches) != 1:
        raise ValueError("0.009 design grid map is not a partition")
    return matches[0]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--start-index", type=int, required=True)
    parser.add_argument("--stop-index", type=int, required=True)
    args = parser.parse_args()
    if (args.start_index, args.stop_index) not in SEGMENTS:
        parser.error("segment is not in the frozen design partition")
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    worst = None
    histogram = {192: 0, 384: 0}
    print("R4 009 BAND-GAP FIXED COVER DESIGN", "segment",
          args.start_index, args.stop_index, "grid_ranges", GRID_RANGES,
          "physical_inner", cover.PHYSICAL_INNER, flush=True)
    for index in range(args.start_index, args.stop_index):
        lo, hi = boxes[index]
        grid = grid_for(index)
        try:
            radius, c4, value, margin = cover.judge_t(lo, hi, grid)
        except (ValueError, ZeroDivisionError) as exc:
            print("ROW DESIGN FAIL", index, grid, type(exc).__name__,
                  str(exc), flush=True)
            return 1
        lower = arb(margin.lower())
        print("ROW", index, "t", lo, hi, "grid", grid, "radius", radius,
              "Y4", c4, "C_value", value, "margin_lower", lower,
              flush=True)
        if radius != cover.Fraction(62, 5) or not lower > 0:
            print("ROW DESIGN FAIL", index, grid, "NONPOSITIVE", flush=True)
            return 1
        histogram[grid] += 1
        if worst is None or lower < worst[0]:
            worst = (lower, index)
    print("R4 009 BAND-GAP FIXED COVER DESIGN SEGMENT PASS",
          args.start_index, args.stop_index, "rows",
          args.stop_index-args.start_index, "histogram", histogram,
          "worst_index", worst[1], "worst_margin_lower", worst[0],
          "PRODUCTION REQUIRED", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

