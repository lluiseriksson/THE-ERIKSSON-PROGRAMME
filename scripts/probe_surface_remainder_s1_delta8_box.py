"""Design probe for one exact delta-eight S1''' seven-carrier box."""

from __future__ import annotations

import argparse
from fractions import Fraction
from time import perf_counter

from flint import arb, ctx

import surface_remainder_s1_delta8_exact as exact
import surface_remainder_s2_delta8_exact as base


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--delta-lo", required=True)
    parser.add_argument("--delta-hi", required=True)
    parser.add_argument("--center-grid", type=int, required=True)
    parser.add_argument("--remainder-grid", type=int, required=True)
    parser.add_argument("--center-mesh-power", type=Fraction, default=Fraction(1))
    parser.add_argument(
        "--remainder-mesh-power", type=Fraction, default=Fraction(1)
    )
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--precision", type=int, default=180)
    args = parser.parse_args()
    ctx.prec = args.precision
    started = perf_counter()
    enclosures, center, box = exact.centered_half_second_enclosures(
        arb(args.delta_lo),
        arb(args.delta_hi),
        arb("2.9"),
        args.center_grid,
        args.remainder_grid,
        workers=args.workers,
        center_mesh_power=args.center_mesh_power,
        remainder_mesh_power=args.remainder_mesh_power,
    )
    fractions = exact.single_box_fractions(
        enclosures, arb(args.delta_lo), arb(args.delta_hi)
    )
    print("S1 DELTA-EIGHT BOX DESIGN")
    print(
        "delta",
        args.delta_lo,
        args.delta_hi,
        "grids",
        args.center_grid,
        args.remainder_grid,
        "mesh_powers",
        args.center_mesh_power,
        args.remainder_mesh_power,
        "workers",
        args.workers,
    )
    for name in exact.NAMES:
        coefficient8 = (box[name].coeffs() + [arb(0)] * base.PREC)[8]
        print(
            name,
            "half_second",
            enclosures[name],
            "half_second_abs_upper",
            enclosures[name].abs_upper(),
            "box_coefficient8",
            coefficient8,
            "single_box_fraction",
            fractions[name],
        )
    print("elapsed_seconds", perf_counter() - started)
    print("DESIGN ONLY; NO S1''' OR K4 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
