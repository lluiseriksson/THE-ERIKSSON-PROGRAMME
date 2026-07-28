"""Run the complete R6 outer/annulus accounting on one born t box.

This is a diagnostic wrapper around the existing split-domain judge.  It is
kept separate from the three-witness and production drivers so that the
annulus-inclusive scope is measured before any transcript is admitted.
"""

from __future__ import annotations

import argparse
from fractions import Fraction

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r6_extension_010_cover as cover


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, required=True)
    parser.add_argument("--grid", type=int, required=True)
    args = parser.parse_args()
    boxes = list(regular.sealed.born_t_boxes())
    if not 0 <= args.index < len(boxes):
        raise ValueError("index outside born t partition")
    ctx.prec = 140
    lo, hi = boxes[args.index]
    print("R6 ANNULUS-INCLUSIVE SINGLE-BOX PROBE", args.index,
          "t", lo, hi, "grid", args.grid, flush=True)
    try:
        radius, head, coefficient5, value, margin = cover.judge_t(
            lo, hi, args.grid)
    except Exception as exc:  # diagnostic transcript must expose failures
        print("DIAGNOSTIC FAIL", type(exc).__name__, str(exc), flush=True)
        return 1
    lower = arb(margin.lower())
    print("RESULT radius", radius, "head", head,
          "Y5", coefficient5, "value", value,
          "margin_lower", lower, flush=True)
    print("R6 ANNULUS-INCLUSIVE SINGLE-BOX PASS" if lower > 0
          else "R6 ANNULUS-INCLUSIVE SINGLE-BOX FAIL", flush=True)
    print("SCOPE diagnostic only; no K2/H_tail/G2/G6 promotion", flush=True)
    return 0 if lower > 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
