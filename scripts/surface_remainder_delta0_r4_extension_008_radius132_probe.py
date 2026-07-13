"""Registered minimal-comfort physical split giving radius 13.2 at 0.008."""

from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_008_split_probe as base


PHYSICAL_INNER = Fraction(1181, 1000)


def main():
    ctx.prec = 140
    boxes = list(regular.sealed.born_t_boxes())
    passed = True
    print("R4 008 RADIUS 13.2 PROBE", "physical_inner", PHYSICAL_INNER,
          "box_indices", base.BOX_INDICES, "grid", base.GRID, flush=True)
    for index in base.BOX_INDICES:
        lo, hi = boxes[index]
        try:
            radius, c4, value, margin = base.judge(
                lo, hi, PHYSICAL_INNER)
        except (ValueError, ZeroDivisionError) as exc:
            print("TRY", index, "UNRESOLVED", type(exc).__name__, str(exc),
                  flush=True)
            passed = False
            continue
        lower = arb(margin.lower())
        print("TRY", index, "radius", radius, "Y4", c4,
              "C_value", value, "margin_lower", lower, flush=True)
        passed = passed and radius == Fraction(66, 5) and lower > 0
    if passed:
        print("R4 008 RADIUS 13.2 DESIGN PASS; EXHAUSTIVE COVER REQUIRED",
              flush=True)
        return 0
    print("R4 008 RADIUS 13.2 DESIGN FAIL", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
