"""Diagnostic gauge-cancellation probe for one R6 annulus box.

This does not certify K2.  It applies the exact identity
    KD*HDF-KF*HDD = KD*(HDF-lambda*HDD)
                          -(KF-lambda*KD)*HDD
to signed interval moment sums before forming the normalized coefficient.
The annulus and finite-delta companion tail are deliberately incomplete.
"""

from __future__ import annotations

import argparse
from fractions import Fraction

from flint import arb, arb_series, ctx

import probe_surface_remainder_r6_companion_charge as exact
import probe_surface_remainder_r6_signed_annulus as signed
import surface_remainder_delta0_extension_probe as regular
from surface_remainder_delta0_r6_extension_010_cover import assemble_y_six
from surface_remainder_arb_jet2 import hull


def midpoint(value: arb) -> arb:
    return (arb(value.lower()) + arb(value.upper())) / 2


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, default=0)
    parser.add_argument("--grid-width", type=Fraction, default=Fraction(1, 2))
    args = parser.parse_args()
    ctx.prec = 120
    boxes = list(regular.sealed.born_t_boxes())
    lo, hi = boxes[args.index]
    t = hull(regular.aq(lo), regular.aq(hi))
    print("R6 GAUGE BOX DIAGNOSTIC", args.index, "t", lo, hi, flush=True)
    core, _ = exact.moment_series(lo, hi)
    annulus = signed.signed_annulus(
        Fraction(0), Fraction(1, 100), t, width=args.grid_width)
    combined = {name: core[name] + annulus[name] for name in core}
    raw = assemble_y_six(combined, t)

    # A fixed scalar lambda is enough for the identity.  The midpoint of the
    # two nominal ratios minimizes the leading-order absolute two-term bound.
    kd0 = midpoint(combined["kd"].coeffs()[0])
    hdd0 = midpoint(combined["hdd"].coeffs()[0])
    r1 = midpoint(combined["hdf"].coeffs()[0]) / hdd0
    r2 = midpoint(combined["kf"].coeffs()[0]) / kd0
    lam = (r1 + r2) / 2
    gauged = dict(combined)
    gauged["hdf"] = combined["hdf"] - lam * combined["hdd"]
    gauged["kf"] = combined["kf"] - lam * combined["kd"]
    gauged_y = assemble_y_six(gauged, t)

    raw_coeffs = raw.coeffs() + [arb(0)] * 8
    gauged_coeffs = gauged_y.coeffs() + [arb(0)] * 8
    print("lambda", lam.str(24), "r1", r1.str(18), "r2", r2.str(18), flush=True)
    print("RAW_Y5", raw_coeffs[5].str(24), flush=True)
    print("GAUGED_Y5", gauged_coeffs[5].str(24), flush=True)
    print("IDENTITY_CHECK", (raw_coeffs[5] - gauged_coeffs[5]).str(12), flush=True)
    print("SCOPE diagnostic only; no K2/H_tail/G2/G6 promotion", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
