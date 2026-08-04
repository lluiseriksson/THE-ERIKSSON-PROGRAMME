"""Sequential Arb design cover of the full scaled G5 rectangle.

The lambda partition has 75 exact boxes of width 1/50.  Delta is kept in a
single zero-based box [0,1/125].  Central chart enclosures are enlarged by
the analytic five-family tail budgets before P0 and H are assembled.
"""

import argparse
import hashlib
from pathlib import Path
import platform

import flint
from flint import arb, ctx

import surface_right_edge_five_family_central_design as central
import surface_right_edge_five_family_tail_design as tail
from surface_remainder_arb_jet2 import hull


ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/surface_right_edge_five_family_cover_design.py",
    "scripts/surface_right_edge_five_family_central_design.py",
    "scripts/surface_right_edge_five_family_tail_design.py",
    "scripts/surface_bessel_integral_remainder.py",
    "scripts/surface_right_edge_scaled_paired_design.py",
    "scripts/surface_remainder_arb_jet2.py",
    "scripts/surface_remainder_delta0_geometry.py",
    "scripts/surface_remainder_centered_prefactor.py",
    "scripts/surface_remainder_carrier_jet.py",
    "scripts/surface_remainder_core_l2_arb.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def family_tail_budgets():
    near_u, near_b = tail.near_tail_bounds()
    far_u, far_b = tail.far_tail_bounds()
    return (
        near_u[1]+far_u[1], near_u[3]+far_u[3],
        near_u[5]+far_u[5], near_b[2]+far_b[2],
        near_b[4]+far_b[4],
    )


def judge(index, budgets, delta_index=None):
    if delta_index is None:
        delta = hull(arb(0), arb(1)/125)
    else:
        if not 0 <= delta_index < 8:
            raise ValueError("delta_index outside the eight-box partition")
        delta = hull(arb(delta_index)/1000, arb(delta_index+1)/1000)
    lam = hull(arb(index)/50, arb(index+1)/50)
    values = central.central_families(
        delta, lam, side=4, qgrid=80, rgrid=16,
        thetagrid=4, phigrid=4)
    def enlarge(row):
        return tuple(value+budget*arb("0 +/- 1")
                     for value, budget in zip(row, budgets))
    enlarged = enlarge(values)
    p0, h = central.assemble_h(delta, lam, enlarged)
    if arb(enlarged[3].lower()) > 0 and arb(p0.lower()) > 0:
        return "coarse", enlarged, p0, h
    # Preserve the already adequate U0 and U2 boxes.  Only the three
    # dominant families receive the doubled one-dimensional grids.
    mixed = (
        values[0],
        central.integrate_u_family(
            delta, lam, 3, side=4, qgrid=160, rgrid=32,
            thetagrid=8, phigrid=1),
        values[2],
        central.integrate_b_family(
            delta, lam, 2, side=4, qgrid=160, rgrid=32,
            thetagrid=1),
        central.integrate_b_family(
            delta, lam, 4, side=4, qgrid=160, rgrid=32,
            thetagrid=8),
    )
    enlarged = enlarge(mixed)
    p0, h = central.assemble_h(delta, lam, enlarged)
    return "mixed", enlarged, p0, h


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int, default=75)
    parser.add_argument("--delta-start", type=int, default=0)
    parser.add_argument("--delta-stop", type=int, default=8)
    args = parser.parse_args()
    if not 0 <= args.start < args.stop <= 75:
        parser.error("require 0<=start<stop<=75")
    if not 0 <= args.delta_start < args.delta_stop <= 8:
        parser.error("require 0<=delta-start<delta-stop<=8")
    ctx.prec = 140
    print("PROVENANCE python", platform.python_version(),
          "python_flint", flint.__version__, "arb_bits", ctx.prec, flush=True)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(ROOT/relative), flush=True)
    print("CONFIG delta_partition 0:1/125:1/1000 "
          "lambda_partition 0:3/2:1/50 "
          "coarse side 4 qgrid 80 rgrid 16 thetagrid 4 phigrid 4 "
          "mixed U0/U2=coarse U1 qgrid160 rgrid32 thetagrid8 phigrid1 "
          "B0 qgrid160 rgrid32 thetagrid1 "
          "B1 qgrid160 rgrid32 thetagrid8", flush=True)
    budgets = family_tail_budgets()
    print("TAILS", *(item.str(20) for item in budgets), flush=True)
    worst = None
    for delta_index in range(args.delta_start, args.delta_stop):
        for index in range(args.start, args.stop):
            resolution, families, p0, h = judge(
                index, budgets, delta_index)
            p_lower, h_lower = arb(p0.lower()), arb(h.lower())
            b_lower = arb(families[3].lower())
            print("ROW", "delta_index", delta_index, "delta",
                  f"{delta_index}/1000:{delta_index+1}/1000",
                  "lambda_index", index, "lambda",
                  f"{index}/50:{index+1}/50", "resolution", resolution,
                  "B0_lower", b_lower.str(30),
                  "P0_lower", p_lower.str(30),
                  "H_lower", h_lower.str(30), flush=True)
            if not b_lower > 0 or not p_lower > 0 or not h_lower > 0:
                for name, value in zip(
                        ("U0", "U1", "U2", "B0", "B1"), families):
                    print("FAIL_FAMILY", name,
                          "lower", value.lower().str(30),
                          "upper", value.upper().str(30), flush=True)
                print("FIVE-FAMILY COVER DESIGN FAIL", delta_index, index,
                      flush=True)
                return 1
            if worst is None or h_lower < worst[0]:
                worst = (h_lower, delta_index, index)
    print("FIVE-FAMILY COVER DESIGN PASS delta", args.delta_start,
          args.delta_stop, "lambda", args.start, args.stop,
          "worst_delta_index", worst[1], "worst_lambda_index", worst[2],
          "worst_H_lower", worst[0],
          "PRODUCTION FREEZE AND INDEPENDENT AUDIT REQUIRED", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
