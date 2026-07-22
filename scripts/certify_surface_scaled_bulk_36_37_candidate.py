"""Provenance-bearing order-13 candidate for scaled bulk [36,37]."""

import argparse
from fractions import Fraction
import hashlib
from pathlib import Path
import platform
import subprocess

import flint
from flint import ctx

import certify_bulk_beta_taylor_scaled_design as scaled

ROOT = Path(__file__).resolve().parents[1]
LO, HI, STEP = Fraction(36), Fraction(37), Fraction(1, 8)
ORDER, T_ORDER = 12, 13
DEPENDENCIES = (
    "scripts/certify_surface_scaled_bulk_36_37_candidate.py",
    "scripts/certify_bulk_beta_taylor_scaled_design.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def head() -> str:
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lo", type=Fraction, default=LO)
    parser.add_argument("--hi", type=Fraction, default=HI)
    args = parser.parse_args()
    ctx.prec = 180
    print("PROVENANCE git_head", head(), flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", flint.__version__, flush=True)
    print("PROVENANCE arb_bits", ctx.prec, flush=True)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(ROOT / relative), flush=True)
    print("CONFIG beta", args.lo, args.hi, "step", STEP,
          "CWIN 4 beta_order", ORDER, "t_order", T_ORDER, flush=True)
    scaled.install_design_backend()
    scaled.bulk.CWIN = Fraction(4)
    total = scaled.bulk.cover(args.lo, args.hi, db=STEP,
                              prec=180, order=ORDER, t_order=T_ORDER)
    print("CANDIDATE SCALED BULK [36,37] beta_boxes", int((args.hi-args.lo)/STEP),
          "t_boxes", total, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
