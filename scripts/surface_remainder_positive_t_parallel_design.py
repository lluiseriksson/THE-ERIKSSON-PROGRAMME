"""Parallel design runner for the repaired positive K2 stress box.

This file emits design evidence only.  The terminal driver must additionally
charge the order-six Bessel companion and the sixth delta-Taylor tail, print
provenance, cover every born box, and be manifested.
"""

import argparse
from time import perf_counter

from flint import arb, ctx

import surface_remainder_positive_t_centered as remainder


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid", type=int, default=32)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--track", choices=("center", "box"), default="center")
    args = parser.parse_args()
    ctx.prec = 120
    delta = arb("0.04975")
    perturbation = arb("0 +/- 0.00025")
    tlo, thi = arb("2.9"), arb("2.92")
    tcenter = (tlo+thi)/2
    t_eval = (tcenter if args.track == "center"
              else remainder.spatial.hull(tlo, thi))
    started = perf_counter()
    value, cells, _ = remainder.parallel_uniform_residual_track(
        delta, t_eval, perturbation, grid=args.grid, workers=args.workers)
    print("PARALLEL_DESIGN", args.track, "grid", args.grid,
          "workers", args.workers, "cells", cells)
    print("R", value.v, "D1", value.d, "D2", value.d2,
          "D3", value.d3, "D4", value.d4)
    print("ELAPSED_SECONDS", perf_counter()-started)


if __name__ == "__main__":
    main()
