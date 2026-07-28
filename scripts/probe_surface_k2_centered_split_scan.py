"""Diagnostic scan of physical split for centered K2 direct evaluation."""

from __future__ import annotations

from fractions import Fraction

from flint import arb, arb_series, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v7 as outer
from surface_remainder_s2_direct_judge import closed_forms


INDEX = 144
DLO = Fraction(9, 1000)
DHI = Fraction(1, 100)
CENTER = Fraction(19, 2000)
HALF_WIDTH = Fraction(1, 2000)
GRID = 192
PREC = 6
ARB_BITS = 140
SPLITS = (Fraction(1181, 1000), Fraction(119, 100), Fraction(1199, 1000))


def evaluate(series, x):
    value = arb(0)
    for coefficient in reversed(series.coeffs()):
        value = value*x + coefficient
    return value


def main() -> int:
    ctx.prec = ARB_BITS
    boxes = list(regular.sealed.born_t_boxes())
    lo, hi = boxes[INDEX]
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    center = regular.aq(CENTER)
    source = regular.parallel_integrate_coefficients(center, t, GRID)
    d = arb_series([center, arb(1)], PREC)
    x = regular.hull(-regular.aq(HALF_WIDTH), regular.aq(HALF_WIDTH))
    leading, r2, _, theta = closed_forms(t)
    for split in SPLITS:
        bounds = outer.outer_derivative_bounds_box_to(DLO, DHI, split)
        moments = {
            name: arb_series([
                source[name].coeffs()[k] + bounds[name][k]*arb("0 +/- 1")
                for k in range(PREC)], PREC)
            for name in source
        }
        bilinear = moments["kd"]*moments["hdf"] - moments["kf"]*moments["hdd"]
        y = 4*(bilinear/d)/moments["kd"]**2
        y_box = evaluate(y, x)
        delta = center+x
        residual = arb((y_box-(leading+r2*delta)).abs_upper())
        budget = theta*regular.aq(DLO)**2
        print("SPLIT", split, "KD_lower", moments["kd"].coeffs()[0].lower(),
              "Y_box", y_box, "residual_abs", residual,
              "budget_min", budget,
              "raw_margin_lower", arb((budget-residual).lower()), flush=True)
    print("CENTERED SPLIT SCAN COMPLETE; NO R3 PROMOTION", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
