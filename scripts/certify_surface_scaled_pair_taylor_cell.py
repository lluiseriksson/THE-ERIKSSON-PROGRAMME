"""Certificate-grade finite cell for the scaled pair-sum bridge.

The driver proves one rational (beta, lambda) cell by adding four outward
rounded quantities: the retained bivariate Taylor polynomial, the explicit
mode tail, and independent beta/lambda Taylor remainder majorants.  It is a
cell primitive only; no global G2 promotion is implied by a successful row.
"""

from __future__ import annotations

import argparse
import hashlib
import platform
import subprocess
from fractions import Fraction
from pathlib import Path

import flint
from flint import ctx

from surface_scaled_pair_taylor_design import pair_taylor
from surface_scaled_pair_taylor_remainder_design import remainder_majorant


ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def head() -> str:
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def parse_fraction(value: str) -> Fraction:
    return Fraction(value)


def run(args) -> str:
    beta_lo, beta_hi = parse_fraction(args.beta_lo), parse_fraction(args.beta_hi)
    lambda_lo, lambda_hi = parse_fraction(args.lambda_lo), parse_fraction(args.lambda_hi)
    if not (beta_lo < beta_hi and lambda_lo <= lambda_hi):
        raise ValueError("invalid rational cell")
    ctx.prec = args.precision
    beta_mid, beta_radius = (beta_lo + beta_hi) / 2, (beta_hi - beta_lo) / 2
    lambda_mid, lambda_radius = (lambda_lo + lambda_hi) / 2, (lambda_hi - lambda_lo) / 2
    finite, mode_tail, _ = pair_taylor(
        beta_mid, beta_radius, lambda_mid, lambda_radius,
        modes=args.modes, beta_order=args.beta_order,
        lambda_order=args.lambda_order, precision=args.precision)
    # The derivative majorant is evaluated independently of the retained
    # Taylor order.  Its beta order is intentionally fixed by the CLI so the
    # transcript states the exact remainder contract.
    lambda_rem, beta_rem = remainder_majorant(
        beta_lo, beta_hi, lambda_mid, lambda_radius,
        modes=args.modes, beta_order=args.remainder_beta_order,
        lambda_order=args.lambda_order, precision=args.precision)
    total_upper = (finite.upper() + mode_tail.upper() +
                   lambda_rem.upper() + beta_rem.upper())
    dependencies = [
        "scripts/certify_surface_scaled_pair_taylor_cell.py",
        "scripts/surface_scaled_pair_taylor_design.py",
        "scripts/surface_scaled_pair_taylor_remainder_design.py",
        "scripts/probe_surface_scaled_pair_sum.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
    ]
    lines = [
        "SCALED PAIR TAYLOR CELL CERTIFICATE",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {head()}",
        (f"config beta_order {args.beta_order} remainder_beta_order "
         f"{args.remainder_beta_order} lambda_order {args.lambda_order} "
         f"modes {args.modes} precision {args.precision}"),
        f"beta_cell {beta_lo} {beta_hi}",
        f"lambda_cell {lambda_lo} {lambda_hi}",
        f"finite {finite.str(100)}",
        f"mode_tail {mode_tail.str(100)}",
        f"lambda_remainder {lambda_rem.str(100)}",
        f"beta_remainder {beta_rem.str(100)}",
        f"total_upper {total_upper.str(100)}",
    ]
    for relative in dependencies:
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    if not total_upper < 0:
        lines.append("SCALED PAIR TAYLOR CELL FAIL")
        raise RuntimeError("cell upper endpoint is not strictly negative")
    lines.append("SCALED PAIR TAYLOR CELL PASS")
    lines.append("SCOPE one rational cell only; no G2/G6 promotion")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta-lo", required=True)
    parser.add_argument("--beta-hi", required=True)
    parser.add_argument("--lambda-lo", required=True)
    parser.add_argument("--lambda-hi", required=True)
    parser.add_argument("--modes", type=int, default=115)
    parser.add_argument("--beta-order", type=int, default=50)
    parser.add_argument("--remainder-beta-order", type=int, default=30)
    parser.add_argument("--lambda-order", type=int, default=28)
    parser.add_argument("--precision", type=int, default=500)
    args = parser.parse_args()
    print(run(args), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
