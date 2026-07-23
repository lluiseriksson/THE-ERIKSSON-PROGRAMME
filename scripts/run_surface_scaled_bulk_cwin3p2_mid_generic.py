"""Production/replay wrapper for the isolated generic mid-order candidate."""

from __future__ import annotations

import argparse
from fractions import Fraction
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_scaled_bulk_cwin3p2_mid_generic.py"


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    parser.add_argument("--unit", required=True)
    parser.add_argument("--order", type=int, default=20)
    parser.add_argument("--t-order", type=int, default=25)
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    suffix = "_rerun" if args.replay else ""
    out = ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}{suffix}.txt"
    result = subprocess.run([sys.executable, str(DRIVER), "--lo", args.lo, "--hi", args.hi, "--unit", args.unit, "--order", str(args.order), "--t-order", str(args.t_order)], cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=None)
    out.write_text(result.stdout, encoding="utf-8")
    if result.returncode:
        raise SystemExit(result.returncode)
    print("CWIN3P2 MID GENERIC", args.unit, "REPLAY" if args.replay else "PRODUCTION", "PASS")
