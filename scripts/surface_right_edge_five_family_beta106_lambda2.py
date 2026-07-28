"""Candidate five-family cover for the beta frontier, lambda in [3/2,2].

This is a separate, parameterized ledger.  It does not modify the existing
G5 implementation: the only changed analytic charge is the near-chart
factor exp(lambda_max), with lambda_max=2 instead of the old 3/2.
"""

from __future__ import annotations

import argparse
import hashlib
import platform
import subprocess
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, ctx

import surface_right_edge_five_family_beta20_design as beta20
import surface_right_edge_five_family_central_design as central
import surface_right_edge_five_family_finite_tail_design as finite_tail
import surface_right_edge_five_family_tail_design as halfline_tail
from surface_remainder_arb_jet2 import hull

ROOT = Path(__file__).resolve().parents[1]
DELTA_LO = Fraction(9, 1000)
DELTA_HI = Fraction(32, 3409)
LAMBDA_LO = Fraction(3, 2)
LAMBDA_HI = Fraction(2)
LAMBDA_STEP = Fraction(1, 50)
SIDE = arb(5) / 2

DEPENDENCIES = (
    "scripts/surface_right_edge_five_family_beta106_lambda2.py",
    "scripts/surface_right_edge_five_family_central_design.py",
    "scripts/surface_right_edge_five_family_finite_tail_design.py",
    "scripts/surface_right_edge_five_family_beta20_design.py",
    "scripts/surface_right_edge_five_family_tail_design.py",
    "scripts/surface_bessel_integral_remainder.py",
    "scripts/surface_right_edge_scaled_paired_design.py",
    "scripts/surface_remainder_arb_jet2.py",
    "docs/SURFACE-G5-BETA106-LAMBDA2-PREREG-20260726.md",
)


def aq(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def near_bounds_lambda2(delta_max: arb):
    """Finite-tail near charge with the registered exp(2) factor."""
    saved = central.reduced_values
    central.reduced_values = finite_tail.low_argument_companion
    try:
        delta = hull(arb(0), delta_max)
        v = hull(finite_tail.VMIN, arb(2))
        i0, i1 = finite_tail.low_argument_companion(delta / v, v)
        gaussian = (4 * arb(2).exp()
                    * halfline_tail.gaussian_one_side(arb(4) / 3,
                                                       finite_tail.SIDE))
        u, b = {}, {}
        for order, weight in (
                (1, 2 / arb.pi()), (3, 1 / (3 * arb.pi())),
                (5, 1 / (30 * arb.pi()))):
            u[order] = (gaussian * weight * arb(i1.abs_upper())
                        * arb(finite_tail.chain("I1", order,
                                                delta_max=delta_max).abs_upper())
                        / 4)
        for order, weight in ((2, 1 / arb.pi()), (4, 2 / (3 * arb.pi()))):
            b[order] = (gaussian * weight * arb(i0.abs_upper())
                        * arb(finite_tail.chain("I0", order, arb(1) / 2,
                                                delta_max=delta_max).abs_upper()))
        return u, b
    finally:
        central.reduced_values = saved


def budgets_lambda2(delta_max: arb):
    nu, nb = near_bounds_lambda2(delta_max)
    fu, fb = finite_tail.far_bounds(delta_max)
    return (nu[1] + fu[1], nu[3] + fu[3], nu[5] + fu[5],
            nb[2] + fb[2], nb[4] + fb[4])


def verify_geometry() -> None:
    if not DELTA_LO < DELTA_HI:
        raise AssertionError("delta interval is not ordered")
    if not LAMBDA_LO < LAMBDA_HI:
        raise AssertionError("lambda interval is not ordered")
    finite_tail.verify_geometry()
    # eta = delta * c and |c| <= lambda/2 on the divided-difference charts.
    eta_max = aq(DELTA_HI * LAMBDA_HI / 2)
    assert eta_max < arb(1) / 100
    assert eta_max < arb(3) / 80
    # The finite chart's old phase-gap geometry remains valid because the
    # angular displacement is strictly smaller than its registered bound.
    assert aq(DELTA_HI * LAMBDA_HI / 2) < aq(Fraction(3, 80))


def judge(lambda_index: int):
    beta20.install(aq(DELTA_HI))
    budgets = budgets_lambda2(aq(DELTA_HI))
    delta = hull(aq(DELTA_LO), aq(DELTA_HI))
    lam = hull(aq(Fraction(lambda_index, 50)),
               aq(Fraction(lambda_index + 1, 50)))
    values = central.central_families(
        delta, lam, side=SIDE, qgrid=80, rgrid=16,
        thetagrid=4, phigrid=4)
    families = tuple(value + budget * arb("0 +/- 1")
                     for value, budget in zip(values, budgets))
    p0, h = central.assemble_h(delta, lam, families)
    if families[3].lower() > 0 and p0.lower() > 0 and h.lower() > 0:
        resolution = "coarse"
    else:
        mixed = (
            central.integrate_u_family(
                delta, lam, 1, side=SIDE, qgrid=160, rgrid=32,
                thetagrid=4, phigrid=1),
            central.integrate_u_family(
                delta, lam, 3, side=SIDE, qgrid=160, rgrid=32,
                thetagrid=8, phigrid=1),
            central.integrate_u_family(
                delta, lam, 5, side=SIDE, qgrid=160, rgrid=32,
                thetagrid=4, phigrid=1),
            central.integrate_b_family(
                delta, lam, 2, side=SIDE, qgrid=160, rgrid=32,
                thetagrid=1),
            central.integrate_b_family(
                delta, lam, 4, side=SIDE, qgrid=160, rgrid=32,
                thetagrid=8),
        )
        families = tuple(value + budget * arb("0 +/- 1")
                         for value, budget in zip(mixed, budgets))
        p0, h = central.assemble_h(delta, lam, families)
        resolution = "mixed"
    return resolution, budgets, families, p0, h


def run(start: int, stop: int) -> str:
    if not 75 <= start < stop <= 100:
        raise ValueError("lambda indices must lie in [75,100]")
    ctx.prec = 140
    verify_geometry()
    rows = []
    for index in range(start, stop):
        resolution, budgets, families, p0, h = judge(index)
        b_lower = arb(families[3].lower())
        p_lower, h_lower = arb(p0.lower()), arb(h.lower())
        if not b_lower > 0 or not p_lower > 0 or not h_lower > 0:
            raise RuntimeError(f"strict sign failure at lambda index {index}")
        rows.append((index, resolution, b_lower, p_lower, h_lower))
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    lines = [
        "G5 BETA106 LAMBDA2 CANDIDATE",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {head}",
        f"delta_domain {DELTA_LO} {DELTA_HI}",
        f"lambda_domain {start}/50 {stop}/50",
        "config lambda_max 2 near_exp exp(2) qgrid 80/160 rgrid 16/32",
        "geometry eta_max < 1/100 < 3/80; phase_gap inherited and checked",
    ]
    for relative in DEPENDENCIES:
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    for index, resolution, b, p0, h in rows:
        lines.append(
            f"ROW lambda_index {index} lambda {index}/50:{index+1}/50 "
            f"resolution {resolution} B0_lower {b.str(30)} "
            f"P0_lower {p0.str(30)} H_lower {h.str(30)}")
    lines.extend([
        f"rows {len(rows)}",
        "G5 BETA106 LAMBDA2 CANDIDATE PASS",
        "SCOPE candidate only; no G2/G6 promotion",
    ])
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--stop", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    text = run(args.start, args.stop)
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")
