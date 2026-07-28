"""Isolated K2 representation smoke; never a production certificate.

The current r4 probe adds symmetric outer-tail intervals to every series
coefficient before dividing by the bilinear's first coefficient.  This smoke
replaces only that first coefficient by the exact closed-form r3 identity,
while retaining all other outward-rounded coefficients.  A pass diagnoses a
representation obstruction; it does not validate a cover or a theorem.
"""

import argparse
from fractions import Fraction
import traceback

from flint import arb, arb_series, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v8 as outer
import surface_remainder_delta0_r4_extension_0125_split_probe as registered
from surface_remainder_delta0_r4_extension_0125_split_probe import (
    PHYSICAL_SPLITS, WITNESSES, closed_forms,
)
from surface_remainder_delta0_r4_extension_probe import PREC
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four


def stabilized(moments, t):
    bilinear = moments["kd"]*moments["hdf"] - moments["kf"]*moments["hdd"]
    coefficients = bilinear.coeffs() + [arb(0)]*PREC
    r3 = closed_forms(t)[2]
    kd0 = moments["kd"].coeffs()[0]
    coefficients[1] = kd0**2*r3/4
    print("DIAGNOSTIC kd0", kd0, "bilinear_lead", coefficients[1],
          "denominator_lead", (kd0**2/4), flush=True)
    quotient = arb_series(coefficients[1:PREC], PREC-1)
    denominator = moments["kd"]**2/4
    print("DIAGNOSTIC q0", quotient.coeffs()[0], "den0",
          denominator.coeffs()[0], flush=True)
    return quotient/denominator


def judge(split, witness, grid):
    boxes = list(regular.sealed.born_t_boxes())
    # Cache entries are precision-sensitive in the legacy outer wrapper; a
    # fresh diagnostic must not reuse a lower-precision annulus enclosure.
    outer.v6.annulus_derivative_bounds_box_to.cache_clear()
    outer.v6.outer_derivative_bounds_box_to.cache_clear()
    nominal = outer.v6.v3.v2.nominal_moment_series
    def traced_nominal(base, t, sigma, tau, prec=6):
        try:
            return nominal(base, t, sigma, tau, prec)
        except Exception:
            print("DIAGNOSTIC NOMINAL FAILURE base", base, "t", t,
                  "sigma", sigma, "tau", tau, flush=True)
            raise
    outer.v6.v3.v2.nominal_moment_series = traced_nominal
    index, _ = witness
    lo, hi = boxes[index]
    original = registered.assemble_y_through_four
    registered.assemble_y_through_four = stabilized
    try:
        return registered.judge(lo, hi, grid, split)
    finally:
        registered.assemble_y_through_four = original
        outer.v6.v3.v2.nominal_moment_series = nominal


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--split-index", type=int, choices=range(4), default=1)
    parser.add_argument("--witness-index", type=int, choices=range(3), default=0)
    parser.add_argument("--grid", type=int, default=192)
    parser.add_argument("--delta-slices", type=int, choices=(1, 2, 4, 8), default=1)
    args = parser.parse_args()
    ctx.prec = 140
    split = PHYSICAL_SPLITS[args.split_index]
    witness = WITNESSES[args.witness_index]
    print("K2 LEADING-TERM SMOKE split", split, "witness", witness,
          "grid", args.grid, "delta_slices", args.delta_slices, flush=True)
    if args.delta_slices > 1:
        original_annulus = outer.v6.annulus_derivative_bounds_box_to
        def split_annulus(delta_lo, delta_hi, physical_inner,
                          inner=12, outer_radius=32, width=Fraction(1, 2)):
            pieces = []
            step = (delta_hi-delta_lo)/args.delta_slices
            for j in range(args.delta_slices):
                a = delta_lo + j*step
                b = delta_lo + (j+1)*step
                pieces.append(original_annulus(
                    a, b, physical_inner, inner, outer_radius, width))
            return {name: [sum((piece[name][k] for piece in pieces), arb(0))
                           for k in range(len(pieces[0][name]))]
                    for name in pieces[0]}
        outer.v6.annulus_derivative_bounds_box_to = split_annulus
        outer.v6.annulus_derivative_bounds_box_to.cache_clear = lambda: None
        original_annulus.cache_clear()
        outer.v6.outer_derivative_bounds_box_to.cache_clear()
    try:
        print("COEFFICIENTS", judge(split, witness, args.grid), flush=True)
        print("REPRESENTATION SMOKE PASS; NO COVER CLAIM", flush=True)
        return 0
    except (ValueError, ZeroDivisionError) as exc:
        traceback.print_exc()
        print("REPRESENTATION SMOKE UNRESOLVED", type(exc).__name__, str(exc),
              flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
