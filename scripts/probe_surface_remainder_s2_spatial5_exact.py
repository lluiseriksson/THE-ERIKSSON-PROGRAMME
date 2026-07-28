"""Design probe for the exact spatial-five S2''' carrier.

No transcript from this driver is certificate evidence.  A production
successor must freeze the delta partition and calibration coefficients,
record full provenance, run replay, and apply the literal weighted judge.
"""

from __future__ import annotations

import argparse
from time import perf_counter

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
import surface_remainder_s2_spatial5_exact as exact


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    result.add_argument("--delta-lo", required=True)
    result.add_argument("--delta-hi", required=True)
    result.add_argument("--grid", type=int, required=True)
    result.add_argument("--workers", type=int, default=4)
    result.add_argument("--precision", type=int, default=160)
    result.add_argument("--q0", required=True)
    result.add_argument("--q1", required=True)
    result.add_argument("--q2", required=True)
    return result


def main() -> int:
    args = parser().parse_args()
    ctx.prec = args.precision
    lo, hi = arb(args.delta_lo), arb(args.delta_hi)
    delta = lo if lo == hi else hull(lo, hi)
    center = (lo + hi) / 2
    coefficients = (arb(args.q0), arb(args.q1), arb(args.q2))
    calibration = exact.calibration_jet(delta, center, coefficients)
    started = perf_counter()
    moments = exact.parallel_uniform_moments(
        delta,
        arb("2.9"),
        args.grid,
        calibration,
        workers=args.workers,
    )
    y = exact.assemble_y(moments, delta)
    print("S2 SPATIAL-FIVE EXACT DESIGN")
    print("delta", lo, hi, "grid", args.grid, "workers", args.workers)
    print("calibration", *coefficients)
    print("KD", moments["KD"].c0)
    print("Y", y.c0, y.c1, y.c2)
    print("half_second_abs_upper", y.c2.abs_upper())
    print("elapsed_seconds", perf_counter() - started)
    print("DESIGN ONLY; NO S2''' OR K4 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
