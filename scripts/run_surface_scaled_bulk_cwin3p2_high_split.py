"""Production/replay runner for the explicit-partition candidate driver."""

from fractions import Fraction
import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high_split.py"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    lo, hi = Fraction(args.lo), Fraction(args.hi)
    suffix = "_rerun" if args.replay else ""
    out = ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}_split{suffix}.txt"
    tmp = out.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run(
        [sys.executable, str(DRIVER), "--unit", args.unit,
         "--lo", str(lo), "--hi", str(hi)],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, timeout=None)
    tmp.write_text(result.stdout, encoding="utf-8")
    if result.returncode:
        tmp.replace(out.with_suffix(".failed.txt"))
        raise SystemExit(result.returncode)
    tmp.replace(out)
    print("CWIN3P2 HIGH SPLIT", args.unit,
          "REPLAY" if args.replay else "PRODUCTION", "PASS")


if __name__ == "__main__":
    main()
