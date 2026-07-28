"""One-row operational checkpoint for the frozen 0.009 design cover.

The desktop runner has a shorter wall-clock ceiling than one frozen runtime
segment.  This wrapper changes no mathematical input: it evaluates exactly
one row of the frozen map and emits a terminal design verdict.  Promotion
still requires a validator to see every index 0,...,157 exactly once.
"""

import argparse

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_009_fixed_cover as fixed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, required=True)
    args = parser.parse_args()
    if not 0 <= args.index < 158:
        parser.error("checkpoint index must lie in 0,...,157")
    ctx.prec = 140
    lo, hi = list(regular.sealed.born_t_boxes())[args.index]
    grid = fixed.grid_for(args.index)
    print("R4 009 BAND-GAP CHECKPOINT DESIGN", "index", args.index,
          "grid", grid, "physical_inner", fixed.cover.PHYSICAL_INNER,
          flush=True)
    try:
        radius, c4, value, margin = fixed.cover.judge_t(lo, hi, grid)
    except (ValueError, ZeroDivisionError) as exc:
        print("ROW DESIGN FAIL", args.index, grid, type(exc).__name__,
              str(exc), flush=True)
        return 1
    lower = arb(margin.lower())
    print("ROW", args.index, "t", lo, hi, "grid", grid, "radius", radius,
          "Y4", c4, "C_value", value, "margin_lower", lower, flush=True)
    if radius != fixed.cover.Fraction(62, 5) or not lower > 0:
        print("R4 009 BAND-GAP CHECKPOINT DESIGN FAIL", args.index,
              flush=True)
        return 1
    print("R4 009 BAND-GAP CHECKPOINT DESIGN PASS", args.index,
          "FULL UNION AND PRODUCTION REQUIRED", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

