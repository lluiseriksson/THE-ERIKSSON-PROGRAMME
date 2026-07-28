"""Pre-registered dyadic tail repair for born t boxes 155 and 156."""

import argparse
from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_009_fixed_cover as fixed


INDICES = (155, 156)
MAX_DEPTH = 2
GRID = 384


def subbox(index, depth, part):
    if index not in INDICES:
        raise ValueError("tail repair is restricted to indices 155 and 156")
    if not 1 <= depth <= MAX_DEPTH:
        raise ValueError("tail repair depth must be one or two")
    if not 0 <= part < 2**depth:
        raise ValueError("part is outside its dyadic level")
    lo, hi = list(regular.sealed.born_t_boxes())[index]
    width = (hi-lo)/2**depth
    return lo+part*width, lo+(part+1)*width


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, choices=INDICES, required=True)
    parser.add_argument("--depth", type=int, choices=(1, 2), required=True)
    parser.add_argument("--part", type=int, required=True)
    args = parser.parse_args()
    try:
        lo, hi = subbox(args.index, args.depth, args.part)
    except ValueError as exc:
        parser.error(str(exc))
    ctx.prec = 140
    print("R4 009 BAND-GAP TAIL BISECTION DESIGN", "index", args.index,
          "depth", args.depth, "part", args.part, "t", lo, hi,
          "grid", GRID, "physical_inner", fixed.cover.PHYSICAL_INNER,
          flush=True)
    try:
        radius, c4, value, margin = fixed.cover.judge_t(lo, hi, GRID)
    except (ValueError, ZeroDivisionError) as exc:
        print("TAIL DESIGN FAIL", args.index, args.depth, args.part,
              type(exc).__name__, str(exc), flush=True)
        return 1
    lower = arb(margin.lower())
    print("ROW", args.index, args.depth, args.part, "t", lo, hi,
          "grid", GRID, "radius", radius, "Y4", c4, "C_value", value,
          "margin_lower", lower, flush=True)
    if radius != fixed.cover.Fraction(62, 5) or not lower > 0:
        print("R4 009 BAND-GAP TAIL BISECTION DESIGN FAIL", args.index,
              args.depth, args.part, flush=True)
        return 1
    print("R4 009 BAND-GAP TAIL BISECTION DESIGN PASS", args.index,
          args.depth, args.part, "FULL UNION AND PRODUCTION REQUIRED",
          flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

