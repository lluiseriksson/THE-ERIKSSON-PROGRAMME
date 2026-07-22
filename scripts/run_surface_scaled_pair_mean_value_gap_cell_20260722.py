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
UNIT = "101p96875_101p984375_lambda150_190"
ARGS = [
    "--beta-lo", "101.96875", "--beta-hi", "101.984375",
    "--lambda-lo", "1.5", "--lambda-hi", "1.9",
    "--modes", "115", "--beta-order", "50", "--lambda-order", "50",
    "--precision", "500",
]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    suffix = "_rerun" if args.replay else ""
    output = ROOT / "scripts" / (
        f"surface_scaled_pair_mean_value_gap_cell_{UNIT}{suffix}.txt")
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
    print("SCALED PAIR GAP CELL", UNIT,
          "REPLAY" if args.replay else "PRODUCTION", "PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
