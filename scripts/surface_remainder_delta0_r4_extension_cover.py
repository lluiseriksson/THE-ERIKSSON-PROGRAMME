"""Exhaustive design cover for the exact-r4 regular lane [0,1/200]."""

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_probe as probe


GRID_LADDER = (24, 48, 96, 192, 384)


def main():
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    histogram = {grid: 0 for grid in GRID_LADDER}
    worst = None
    print("R4 COVER DESIGN delta_max 1/200 boxes", len(boxes),
          "grid_ladder", GRID_LADDER, flush=True)
    for index, (lo, hi) in enumerate(boxes):
        passed = None
        for grid in GRID_LADDER:
            try:
                head, c4, value, margin = probe.judge(
                    probe.DELTA_CANDIDATE, lo, hi, grid, parallel=True)
            except (ValueError, ZeroDivisionError) as error:
                print("TRY index", index, "t", lo, hi, "grid", grid,
                      "UNRESOLVED", type(error).__name__, flush=True)
                continue
            lower = arb(margin.lower())
            print("TRY index", index, "t", lo, hi, "grid", grid,
                  "head_r3_r4", head, "Y4", c4, "C_value", value,
                  "margin", margin, "margin_lower", lower, flush=True)
            if lower > 0:
                passed = (grid, lower)
                break
        if passed is None:
            print("R4 COVER DESIGN FAIL index", index, flush=True)
            return 1
        histogram[passed[0]] += 1
        if worst is None or passed[1] < worst[0]:
            worst = (passed[1], index)
        print("ROW PASS index", index, "grid", passed[0],
              "margin_lower", passed[1], flush=True)
    print("R4 COVER DESIGN PASS rows", len(boxes), "histogram", histogram,
          "worst_index", worst[1], "worst_margin_lower", worst[0],
          "PRODUCTION REQUIRED", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
