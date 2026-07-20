"""Run one frozen mean-value candidate cell, with deterministic replay output."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_scaled_pair_mean_value_cell.py"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta-lo", required=True)
    parser.add_argument("--beta-hi", required=True)
    parser.add_argument("--lambda-lo", required=True)
    parser.add_argument("--lambda-hi", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--modes", type=int, default=115)
    parser.add_argument("--beta-order", type=int, default=50)
    parser.add_argument("--lambda-order", type=int, default=50)
    parser.add_argument("--precision", type=int, default=500)
    args = parser.parse_args()
    command = [
        sys.executable, str(DRIVER),
        "--beta-lo", args.beta_lo, "--beta-hi", args.beta_hi,
        "--lambda-lo", args.lambda_lo, "--lambda-hi", args.lambda_hi,
        "--modes", str(args.modes), "--beta-order", str(args.beta_order),
        "--lambda-order", str(args.lambda_order), "--precision", str(args.precision),
    ]
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, timeout=None)
    output = (ROOT / args.output).resolve()
    output.relative_to(ROOT)
    temporary = output.with_suffix(f".{os.getpid()}.tmp")
    if result.returncode:
        temporary.write_text(result.stdout, encoding="utf-8")
        temporary.replace(output.with_suffix(".failed.txt"))
        return result.returncode
    temporary.write_text(result.stdout, encoding="utf-8")
    temporary.replace(output)
    print("SCALED PAIR MEAN-VALUE BAND", "REPLAY" if args.replay else "PRODUCTION", "PASS")
    print(output.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
