"""Run a bounded exact-rational mean-value campaign without promotion.

The launcher fabricates production and replay transcripts for a fixed beta
partition.  It records failures in the console and never writes a manifest or
changes a gate; a separate audit must decide whether a successful subset is a
cover.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts" / "run_surface_scaled_pair_mean_value_band.py"


def decimal(value: Fraction) -> str:
    # Keep every endpoint exact.  The certifier parses Fraction strings
    # itself; converting to float would silently destroy the rational splice
    # at beta=1000/9 and any future non-dyadic boundary.
    return (str(value.numerator) if value.denominator == 1
            else f"{value.numerator}/{value.denominator}")


def slug(value: Fraction) -> str:
    return (str(value.numerator) if value.denominator == 1
            else f"{value.numerator}p{value.denominator}")


def one_cell(args: tuple[Fraction, Fraction, Fraction, Fraction, int, int, int]) -> str:
    blo, bhi, llo, lhi, modes, beta_order, lambda_order = args
    stem = (f"surface_scaled_pair_mean_value_band_beta{slug(blo)}_{slug(bhi)}"
            f"_lambda{slug(llo)}_{slug(lhi)}")
    common = [
        sys.executable, str(RUNNER), "--beta-lo", decimal(blo),
        "--beta-hi", decimal(bhi), "--lambda-lo", decimal(llo),
        "--lambda-hi", decimal(lhi), "--modes", str(modes),
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
    return f"PASS beta={blo}:{bhi} lambda={llo}:{lhi}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta-lo", required=True, type=Fraction)
    parser.add_argument("--beta-hi", required=True, type=Fraction)
    parser.add_argument("--step", required=True, type=Fraction)
    parser.add_argument("--lambda-lo", required=True, type=Fraction)
    parser.add_argument("--lambda-hi", required=True, type=Fraction)
    parser.add_argument("--max-cells", type=int, required=True)
    parser.add_argument("--workers", type=int, choices=(1, 2), default=2)
    args = parser.parse_args()
    if not (args.beta_lo < args.beta_hi and args.step > 0 and args.max_cells > 0):
        parser.error("invalid beta range, step, or max-cells")
    cells = []
    lo = args.beta_lo
    while lo < args.beta_hi and len(cells) < args.max_cells:
        hi = min(lo + args.step, args.beta_hi)
        cells.append((lo, hi, args.lambda_lo, args.lambda_hi, 115, 50, 50))
        lo = hi
    if not cells or cells[-1][1] != args.beta_hi:
        raise SystemExit("max-cells does not reach the requested beta endpoint")
    print(f"MEAN-VALUE CAMPAIGN cells={len(cells)} workers={args.workers}", flush=True)
    failures = 0
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(one_cell, cell) for cell in cells]
        for future in as_completed(futures):
            result = future.result()
            print(result, flush=True)
            failures += int(result.startswith("FAIL"))
    print(f"MEAN-VALUE CAMPAIGN COMPLETE failures={failures}", flush=True)
    print("NO MANIFEST WRITTEN; NO G2/G6 PROMOTION", flush=True)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
