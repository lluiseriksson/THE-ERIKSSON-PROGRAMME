"""Registered intermediate physical splits for the delta=0.008 endpoints."""

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_008_split_probe as base


PHYSICAL_SPLITS = (Fraction(7, 6), Fraction(47, 40), Fraction(71, 60))


def main():
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    print("R4 008 INTERMEDIATE SPLIT PROBE", "splits", PHYSICAL_SPLITS,
          "box_indices", base.BOX_INDICES, "grid", base.GRID, flush=True)
    for split in PHYSICAL_SPLITS:
        passed = True
        for index in base.BOX_INDICES:
            lo, hi = boxes[index]
            try:
                radius, c4, value, margin = base.judge(lo, hi, split)
            except (ValueError, ZeroDivisionError) as exc:
                print("TRY", split, index, "UNRESOLVED", type(exc).__name__,
                      str(exc), flush=True)
                passed = False
                continue
            lower = arb(margin.lower())
            print("TRY", split, index, "radius", radius, "Y4", c4,
                  "C_value", value, "margin_lower", lower, flush=True)
            passed = passed and lower > 0
        print("SPLIT", split, "TWO-ENDPOINT-PASS" if passed else "FAIL",
              flush=True)
        if passed:
            print("R4 008 INTERMEDIATE SPLIT DESIGN PASS", split,
                  "EXHAUSTIVE COVER REQUIRED", flush=True)
            return 0
    print("R4 008 INTERMEDIATE SPLIT DESIGN FAIL", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
