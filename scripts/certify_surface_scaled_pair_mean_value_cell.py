"""Certificate-grade mean-value cell for the scaled pair bridge."""

from __future__ import annotations

import argparse
import hashlib
import platform
import subprocess
from fractions import Fraction
from pathlib import Path

import flint
from flint import ctx

from surface_scaled_pair_mean_value_design import mean_value_cell


ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args) -> str:
    blo, bhi = Fraction(args.beta_lo), Fraction(args.beta_hi)
    llo, lhi = Fraction(args.lambda_lo), Fraction(args.lambda_hi)
    ctx.prec = args.precision
    out = mean_value_cell(
        blo, bhi, llo, lhi, modes=args.modes,
        beta_order=args.beta_order, lambda_order=args.lambda_order,
        precision=args.precision)
    total = out["total_upper"]
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    lines = [
        "SCALED PAIR MEAN-VALUE CELL CERTIFICATE",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {head}",
        (f"config beta_order {args.beta_order} lambda_order "
         f"{args.lambda_order} modes {args.modes} precision {args.precision}"),
        f"beta_cell {blo} {bhi}",
        f"lambda_cell {llo} {lhi}",
    ]
    for name in ("centre", "mode_tail", "slope", "tail_slope",
                 "lambda_remainder", "lambda_beta_remainder",
                 "beta_remainder", "slope_remainder",
                 "total_upper"):
        lines.append(f"{name} {out[name].str(100)}")
    for relative in (
        "scripts/certify_surface_scaled_pair_mean_value_cell.py",
        "scripts/surface_scaled_pair_mean_value_design.py",
        "scripts/surface_scaled_pair_tail_derivative_design.py",
        "scripts/surface_scaled_pair_taylor_design.py",
        "scripts/surface_scaled_pair_taylor_remainder_design.py",
        "scripts/probe_surface_scaled_pair_sum.py",
    ):
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    if not total < 0:
        lines.append("SCALED PAIR MEAN-VALUE CELL FAIL")
        raise RuntimeError("mean-value upper endpoint is not negative")
    lines.append("SCALED PAIR MEAN-VALUE CELL PASS")
    lines.append("SCOPE one beta/lambda cell only; no G2/G6 promotion")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta-lo", required=True)
    parser.add_argument("--beta-hi", required=True)
    parser.add_argument("--lambda-lo", required=True)
    parser.add_argument("--lambda-hi", required=True)
    parser.add_argument("--modes", type=int, default=115)
    parser.add_argument("--beta-order", type=int, default=50)
    parser.add_argument("--lambda-order", type=int, default=50)
    parser.add_argument("--precision", type=int, default=500)
    print(run(parser.parse_args()), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
