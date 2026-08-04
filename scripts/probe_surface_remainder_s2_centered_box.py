"""Design probe for one centred-delta S2''' box."""

from __future__ import annotations

import argparse
from time import perf_counter

from flint import arb, ctx

import surface_remainder_s2_spatial5_exact as exact


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--delta-lo", required=True)
    parser.add_argument("--delta-hi", required=True)
    parser.add_argument("--center-grid", type=int, required=True)
    parser.add_argument("--variation-grid", type=int, required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--precision", type=int, default=180)
    parser.add_argument("--q0", required=True)
    parser.add_argument("--q1", required=True)
    parser.add_argument("--q2", required=True)
    args = parser.parse_args()
    ctx.prec = args.precision
    coefficients = (arb(args.q0), arb(args.q1), arb(args.q2))
    started = perf_counter()
    enclosure, center, whole = exact.centered_half_second_enclosure(
        arb(args.delta_lo),
        arb(args.delta_hi),
        arb("2.9"),
        args.center_grid,
        args.variation_grid,
        coefficients,
        workers=args.workers,
    )
    print("S2 CENTRED BOX DESIGN")
    print(
        "delta",
        args.delta_lo,
        args.delta_hi,
        "grids",
        args.center_grid,
        args.variation_grid,
        "workers",
        args.workers,
    )
    print("calibration", *coefficients)
    print("center_y", *center.derivatives())
    print("whole_y", *whole.derivatives())
    print("half_second", enclosure)
    print("half_second_abs_upper", enclosure.abs_upper())
    print("elapsed_seconds", perf_counter() - started)
    print("DESIGN ONLY; NO S2''' OR K4 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
