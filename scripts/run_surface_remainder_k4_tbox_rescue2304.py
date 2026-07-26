"""Scoped K4 rescue driver with 2,304 cells on both delta segments.

This wrapper reuses the frozen generic driver but replaces its second-segment
budget.  It is intentionally a separate dependency tree so old manifests
remain byte-reproducible and the rescue cannot silently change their claim.
"""

import argparse
import surface_remainder_centered_delta_integrator_design as design
import run_surface_remainder_k4_tbox_endpoint as generic


SEGMENTS = (("0.048", "0.049", 2304), ("0.049", "0.05", 2304))


def run(unit, t_lo, t_hi):
    old = generic.SEGMENTS
    try:
        generic.SEGMENTS = SEGMENTS
        return generic.run(unit, t_lo, t_hi).replace(
            f"K4 ENDPOINT TBOX {unit}",
            f"K4 ENDPOINT TBOX RESCUE2304 {unit}")
    finally:
        generic.SEGMENTS = old


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--t-lo", required=True)
    parser.add_argument("--t-hi", required=True)
    args = parser.parse_args()
    print(run(args.unit, args.t_lo, args.t_hi), end="")
