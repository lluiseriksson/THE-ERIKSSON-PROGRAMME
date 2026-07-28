"""Run/replay one frozen narrow pair-Taylor cell."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_scaled_pair_taylor_cell.py"
UNIT = "narrow_101p8125_101p81275_lambda_1501"
ARGS = [
    "--beta-lo", "101.8125", "--beta-hi", "101.81275",
    "--lambda-lo", "1.501", "--lambda-hi", "1.501",
    "--modes", "115", "--beta-order", "50",
    "--remainder-beta-order", "30", "--lambda-order", "28",
    "--precision", "500",
]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    suffix = "_rerun" if args.replay else ""
    output = ROOT / "scripts" / f"surface_scaled_pair_taylor_cell_{UNIT}{suffix}.txt"
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
    print("SCALED PAIR CELL", UNIT,
          "REPLAY" if args.replay else "PRODUCTION", "PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
