"""Probe only: test the positive-KD cell lower after refining born t-boxes.

This is deliberately not a certificate driver.  It records whether the
pointwise lower implementation can cover the authoritative 158 born boxes
after a uniform t subdivision; promotion still requires a frozen manifest,
independent replay, and the S1/S2 remainder contracts.
"""

import argparse
import json
from pathlib import Path

from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
from surface_remainder_arb_jet2 import hull
from surface_remainder_positive_kd_lower import positive_kd_lower


ROOT = Path(__file__).resolve().parents[1]


def rational_box(lo, hi):
    lo_a = arb(lo.numerator) / arb(lo.denominator)
    hi_a = arb(hi.numerator) / arb(hi.denominator)
    return hull(lo_a, hi_a)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--split", type=int, default=2)
    parser.add_argument("--grid", type=int, default=24)
    parser.add_argument("--delta", default="0.010 +/- 0.0005")
    parser.add_argument("--output", default="")
    parser.add_argument("--max-parents", type=int, default=0)
    parser.add_argument("--start-parent", type=int, default=0)
    args = parser.parse_args()
    if args.split < 1 or args.grid < 1:
        raise SystemExit("split and grid must be positive")
    ctx.prec = 100
    delta = arb(args.delta)
    rows = []
    failures = []
    boxes = list(regular.sealed.born_t_boxes())
    start = max(0, args.start_parent)
    stop = args.max_parents if args.max_parents else len(boxes)
    boxes = boxes[start:stop]
    for local_parent, (lo, hi) in enumerate(boxes):
        parent = start + local_parent
        width = (hi - lo) / args.split
        for part in range(args.split):
            sub_lo = lo + width * part
            sub_hi = lo + width * (part + 1)
            t_box = rational_box(sub_lo, sub_hi)
            try:
                lower, cells = positive_kd_lower(delta, t_box, grid=args.grid)
                row = {
                    "parent": parent,
                    "part": part,
                    "t_lo": f"{sub_lo.numerator}/{sub_lo.denominator}",
                    "t_hi": f"{sub_hi.numerator}/{sub_hi.denominator}",
                    "grid": args.grid,
                    "cells": cells,
                    "lower": lower.str(40),
                    "positive": bool(lower > 0),
                }
                rows.append(row)
                if not row["positive"]:
                    failures.append(row)
            except Exception as error:  # probe diagnostics, not a claim
                row = {
                    "parent": parent,
                    "part": part,
                    "t_lo": f"{sub_lo.numerator}/{sub_lo.denominator}",
                    "t_hi": f"{sub_hi.numerator}/{sub_hi.denominator}",
                    "grid": args.grid,
                    "error": f"{type(error).__name__}: {error}",
                }
                rows.append(row)
                failures.append(row)
        if (local_parent + 1) % 10 == 0:
            print(f"PROBE progress parent={parent + 1} failures={len(failures)}", flush=True)
    result = {
        "kind": "probe_only",
        "delta": args.delta,
        "split": args.split,
        "grid": args.grid,
        "parent_start": start,
        "parent_stop": stop,
        "parents": len(boxes),
        "rows": len(rows),
        "failures": len(failures),
        "rows_data": rows,
    }
    if args.output:
        Path(args.output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("KD T-REFINEMENT PROBE", json.dumps({k: result[k] for k in result if k != "rows_data"}))
    if failures:
        print("FIRST_FAILURE", json.dumps(failures[0], sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
