"""Run/replay the frozen mean-value beta cell."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_scaled_pair_mean_value_cell.py"
UNIT = "beta101p8125_101p84375_lambda150_151"
ARGS = [
    "--beta-lo", "101.8125", "--beta-hi", "101.84375",
    "--lambda-lo", "1.5", "--lambda-hi", "1.51",
    "--modes", "115", "--beta-order", "50", "--lambda-order", "50",
    "--precision", "500",
]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    suffix = "_rerun" if args.replay else ""
    output = ROOT / f"scripts/surface_scaled_pair_mean_value_cell_{UNIT}{suffix}.txt"
    temporary = output.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run(
        [sys.executable, str(DRIVER), *ARGS], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        timeout=None,
    )
    temporary.write_text(result.stdout, encoding="utf-8")
    if result.returncode:
        temporary.replace(output.with_suffix(".failed.txt"))
        raise SystemExit(result.returncode)
    temporary.replace(output)
    print("SCALED PAIR MEAN-VALUE", UNIT,
          "REPLAY" if args.replay else "PRODUCTION", "PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
