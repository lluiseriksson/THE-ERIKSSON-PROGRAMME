"""Arb design cover for the finite G5 bridge ``30 <= beta <= 125``.

Five exact delta bands were fixed after the single-cell adversarial ladder.
Every central enclosure is enlarged by a tail budget recomputed at that
band's upper delta endpoint.  Output remains design evidence until a frozen
production script, validator, and independent execution exist.
"""

import argparse
from fractions import Fraction
import hashlib
from pathlib import Path
import platform

import flint
from flint import arb, ctx

import surface_right_edge_five_family_beta20_design as beta20
import surface_right_edge_five_family_central_design as central
import surface_right_edge_five_family_finite_tail_design as tail
from surface_remainder_arb_jet2 import hull


ROOT = Path(__file__).resolve().parents[1]
DELTA_BANDS = (
    (Fraction(1, 125), Fraction(7, 500)),
    (Fraction(7, 500), Fraction(1, 50)),
    (Fraction(1, 50), Fraction(1, 40)),
    (Fraction(1, 40), Fraction(3, 100)),
    (Fraction(3, 100), Fraction(1, 30)),
)
DEPENDENCIES = (
    "scripts/surface_right_edge_five_family_finite_cover_design.py",
    "scripts/surface_right_edge_five_family_beta20_design.py",
    "scripts/surface_right_edge_five_family_finite_tail_design.py",
    "scripts/surface_right_edge_five_family_tail_design.py",
    "scripts/surface_right_edge_five_family_central_design.py",
    "scripts/surface_bessel_integral_remainder.py",
    "scripts/surface_right_edge_scaled_paired_design.py",
    "scripts/surface_remainder_arb_jet2.py",
    "scripts/surface_remainder_delta0_geometry.py",
)


def aq(value):
    value = Fraction(value)
    return arb(value.numerator)/value.denominator


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fraction_string(value):
    return f"{value.numerator}/{value.denominator}"


def enlarged(values, budgets):
    return tuple(value+budget*arb("0 +/- 1")
                 for value, budget in zip(values, budgets))


def judge(delta_index, lambda_index, delta_bands=None):
    if delta_bands is None:
        delta_bands = DELTA_BANDS
    dlo, dhi = delta_bands[delta_index]
    beta20.install(aq(dhi))
    budgets = tail.budgets(aq(dhi))
    delta = hull(aq(dlo), aq(dhi))
    lam = hull(aq(Fraction(lambda_index, 50)),
               aq(Fraction(lambda_index+1, 50)))
    values = central.central_families(
        delta, lam, side=arb(5)/2, qgrid=80, rgrid=16,
        thetagrid=4, phigrid=4)
    families = enlarged(values, budgets)
    p0, h = central.assemble_h(delta, lam, families)
    if (arb(families[3].lower()) > 0
            and arb(p0.lower()) > 0 and arb(h.lower()) > 0):
        return "coarse", budgets, families, p0, h
    mixed = (
        central.integrate_u_family(
            delta, lam, 1, side=arb(5)/2, qgrid=160, rgrid=32,
            thetagrid=4, phigrid=1),
        central.integrate_u_family(
            delta, lam, 3, side=arb(5)/2, qgrid=160, rgrid=32,
            thetagrid=8, phigrid=1),
        central.integrate_u_family(
            delta, lam, 5, side=arb(5)/2, qgrid=160, rgrid=32,
            thetagrid=4, phigrid=1),
        central.integrate_b_family(
            delta, lam, 2, side=arb(5)/2, qgrid=160, rgrid=32,
            thetagrid=1),
        central.integrate_b_family(
            delta, lam, 4, side=arb(5)/2, qgrid=160, rgrid=32,
            thetagrid=8),
    )
    families = enlarged(mixed, budgets)
    p0, h = central.assemble_h(delta, lam, families)
    return "mixed", budgets, families, p0, h


def main(delta_bands=None, dependencies=None):
    if delta_bands is None:
        delta_bands = DELTA_BANDS
    if dependencies is None:
        dependencies = DEPENDENCIES
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int, default=75)
    args = parser.parse_args()
    if not 0 <= args.start < args.stop <= 75:
        parser.error("require 0<=start<stop<=75")
    ctx.prec = 140
    print("PROVENANCE python", platform.python_version(),
          "python_flint", flint.__version__, "arb_bits", ctx.prec,
          flush=True)
    for relative in dependencies:
        print("DEPENDENCY", relative, sha256(ROOT/relative), flush=True)
    print("CONFIG delta_bands", ",".join(
        fraction_string(lo)+":"+fraction_string(hi)
        for lo, hi in delta_bands),
        "lambda_partition 0:3/2:1/50 side 5/2 "
        "coarse qgrid80 rgrid16 thetagrid4 phigrid4 "
        "mixed qgrid160 rgrid32", flush=True)
    worst = None
    for delta_index, (dlo, dhi) in enumerate(delta_bands):
        for index in range(args.start, args.stop):
            resolution, budgets, families, p0, h = judge(
                delta_index, index, delta_bands)
            b_lower = arb(families[3].lower())
            p_lower, h_lower = arb(p0.lower()), arb(h.lower())
            print("ROW", "delta_index", delta_index, "delta",
                  fraction_string(dlo)+":"+fraction_string(dhi),
                  "lambda_index", index, "lambda",
                  f"{index}/50:{index+1}/50", "resolution", resolution,
                  "B0_lower", b_lower.str(30),
                  "P0_lower", p_lower.str(30),
                  "H_lower", h_lower.str(30), flush=True)
            if not b_lower > 0 or not p_lower > 0 or not h_lower > 0:
                print("FINITE FIVE-FAMILY COVER DESIGN FAIL",
                      delta_index, index, flush=True)
                return 1
            if worst is None or h_lower < worst[0]:
                worst = (h_lower, delta_index, index)
    print("FINITE FIVE-FAMILY COVER DESIGN PASS lambda", args.start,
          args.stop, "rows", len(DELTA_BANDS)*(args.stop-args.start),
          "worst_delta_index", worst[1], "worst_lambda_index", worst[2],
          "worst_H_lower", worst[0],
          "PRODUCTION FREEZE AND INDEPENDENT AUDIT REQUIRED", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
