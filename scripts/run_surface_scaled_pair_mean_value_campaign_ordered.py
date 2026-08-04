"""Bounded paired mean-value campaign with explicit Taylor orders."""

from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
import argparse
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts" / "run_surface_scaled_pair_mean_value_band.py"


def decimal(value):
    return str(value.numerator) if value.denominator == 1 else (
        f"{value.numerator}/{value.denominator}")


def slug(value):
    return str(value.numerator) if value.denominator == 1 else (
        f"{value.numerator}p{value.denominator}")


def one_cell(cell, lambda_lo, lambda_hi, beta_order, lambda_order):
    blo, bhi = cell
    stem = (f"surface_scaled_pair_mean_value_band_beta{slug(blo)}_{slug(bhi)}"
            f"_lambda{slug(lambda_lo)}_{slug(lambda_hi)}")
    common = [
        sys.executable, str(RUNNER), "--beta-lo", decimal(blo),
        "--beta-hi", decimal(bhi), "--lambda-lo", decimal(lambda_lo),
        "--lambda-hi", decimal(lambda_hi), "--modes", "115",
        "--beta-order", str(beta_order), "--lambda-order", str(lambda_order),
        "--precision", "500",
    ]
    for replay, suffix in ((False, ""), (True, "_rerun")):
        command = common + ["--output", f"scripts/{stem}{suffix}.txt"]
        if replay:
            command.append("--replay")
        result = subprocess.run(command, cwd=ROOT, text=True,
                                capture_output=True, check=False)
        if result.returncode:
            return (f"FAIL beta={blo}:{bhi} replay={replay}\n"
                    f"{result.stdout}{result.stderr}")
    return f"PASS beta={blo}:{bhi}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta-lo", required=True, type=Fraction)
    parser.add_argument("--beta-hi", required=True, type=Fraction)
    parser.add_argument("--step", required=True, type=Fraction)
    parser.add_argument("--lambda-lo", required=True, type=Fraction)
    parser.add_argument("--lambda-hi", required=True, type=Fraction)
    parser.add_argument("--beta-order", required=True, type=int)
    parser.add_argument("--lambda-order", required=True, type=int)
    parser.add_argument("--max-cells", required=True, type=int)
    parser.add_argument("--workers", type=int, choices=(1, 2), default=2)
    args = parser.parse_args()
    cells = []
    lo = args.beta_lo
    while lo < args.beta_hi and len(cells) < args.max_cells:
        hi = min(lo + args.step, args.beta_hi)
        cells.append((lo, hi))
        lo = hi
    if not cells or cells[-1][1] != args.beta_hi:
        raise SystemExit("max-cells does not reach requested endpoint")
    print(f"MEAN-VALUE ORDERED CAMPAIGN cells={len(cells)} "
          f"beta_order={args.beta_order} workers={args.workers}", flush=True)
    failures = 0
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(one_cell, cell, args.lambda_lo,
                               args.lambda_hi, args.beta_order,
                               args.lambda_order) for cell in cells]
        for future in as_completed(futures):
            result = future.result()
            print(result, flush=True)
            failures += int(result.startswith("FAIL"))
    print(f"MEAN-VALUE ORDERED CAMPAIGN COMPLETE failures={failures}", flush=True)
    print("NO MANIFEST WRITTEN; NO G2/G6 PROMOTION", flush=True)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
