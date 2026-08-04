"""Production/replay runner for the repaired beta-remainder gap cell.

This is a candidate witness only.  It freezes the first cell after the
continuous pair-Taylor segment and records the explicit beta derivative of
the lambda remainder introduced on 2026-07-22.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_scaled_pair_mean_value_cell.py"
DEFAULT_UNIT = "101p96875_101p984375_lambda150_190"
DEFAULT_ARGS = [
    "--beta-lo", "101.96875", "--beta-hi", "101.984375",
    "--lambda-lo", "1.5", "--lambda-hi", "1.9",
]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--unit", default=DEFAULT_UNIT)
    parser.add_argument("--beta-lo", default=DEFAULT_ARGS[1])
    parser.add_argument("--beta-hi", default=DEFAULT_ARGS[3])
    parser.add_argument("--lambda-lo", default=DEFAULT_ARGS[5])
    parser.add_argument("--lambda-hi", default=DEFAULT_ARGS[7])
    parser.add_argument("--modes", type=int, default=115)
    parser.add_argument("--beta-order", type=int, default=50)
    parser.add_argument("--lambda-order", type=int, default=50)
    parser.add_argument("--precision", type=int, default=500)
    args = parser.parse_args()
    suffix = "_rerun" if args.replay else ""
    output = ROOT / "scripts" / (
        f"surface_scaled_pair_mean_value_gap_cell_{args.unit}{suffix}.txt")
    driver_args = [
        "--beta-lo", args.beta_lo, "--beta-hi", args.beta_hi,
        "--lambda-lo", args.lambda_lo, "--lambda-hi", args.lambda_hi,
        "--modes", str(args.modes), "--beta-order", str(args.beta_order),
        "--lambda-order", str(args.lambda_order),
        "--precision", str(args.precision),
    ]
    temporary = output.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run(
        [sys.executable, str(DRIVER), *driver_args], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        timeout=None,
    )
    temporary.write_text(result.stdout, encoding="utf-8")
    if result.returncode:
        temporary.replace(output.with_suffix(".failed.txt"))
        raise SystemExit(result.returncode)
    temporary.replace(output)
    print("SCALED PAIR GAP CELL", args.unit,
          "REPLAY" if args.replay else "PRODUCTION", "PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
