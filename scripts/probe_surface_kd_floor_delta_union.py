"""Probe a finite delta union for the positive KD lower envelope.

This is diagnostic evidence only. The companion/error and S1/S2 relay ledgers
are intentionally outside this driver, so it cannot promote G2 or G6.
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
    return hull(arb(lo.numerator) / arb(lo.denominator),
                arb(hi.numerator) / arb(hi.denominator))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--delta-lo", default="1/1000")
    parser.add_argument("--delta-hi", default="1/200")
    parser.add_argument("--delta-step", default="1/2000")
    parser.add_argument("--grid", type=int, default=8)
    parser.add_argument("--output", default="probe_kd_delta_union.json")
    args = parser.parse_args()
    ctx.prec = 100
    # Parse rational command-line values without binary floats.
    def frac(text):
        if "/" in text:
            n, d = text.split("/", 1)
            from fractions import Fraction
            return Fraction(int(n), int(d))
        from fractions import Fraction
        return Fraction(text)
    dlo, dhi, step = frac(args.delta_lo), frac(args.delta_hi), frac(args.delta_step)
    if not (dlo < dhi and step > 0):
        raise SystemExit("require delta-lo < delta-hi and positive delta-step")
    dboxes = []
    left = dlo
    while left < dhi:
        right = min(left + step, dhi)
        dboxes.append((left, right))
        left = right
    boxes = list(regular.sealed.born_t_boxes())
    rows = []
    failures = []
    for di, (dleft, dright) in enumerate(dboxes):
        delta = rational_box(dleft, dright)
        for ti, (tleft, tright) in enumerate(boxes):
            try:
                lower, cells = positive_kd_lower(delta, rational_box(tleft, tright), args.grid)
                row = {"delta_index": di, "t_index": ti,
                       "delta_lo": f"{dleft.numerator}/{dleft.denominator}",
                       "delta_hi": f"{dright.numerator}/{dright.denominator}",
                       "cells": cells, "lower": lower.str(40),
                       "positive": bool(lower > 0)}
            except Exception as error:
                row = {"delta_index": di, "t_index": ti,
                       "delta_lo": f"{dleft.numerator}/{dleft.denominator}",
                       "delta_hi": f"{dright.numerator}/{dright.denominator}",
                       "error": f"{type(error).__name__}: {error}",
                       "positive": False}
            rows.append(row)
            if not row["positive"]:
                failures.append(row)
        print(f"PROBE delta={di + 1}/{len(dboxes)} failures={len(failures)}", flush=True)
    payload = {"kind": "probe_only", "grid": args.grid,
               "delta_lo": args.delta_lo, "delta_hi": args.delta_hi,
               "delta_step": args.delta_step, "delta_boxes": len(dboxes),
               "t_boxes": len(boxes), "rows": len(rows),
               "failures": len(failures), "rows_data": rows}
    (ROOT / args.output).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print("KD DELTA UNION PROBE", json.dumps({k: payload[k] for k in payload if k != "rows_data"}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
