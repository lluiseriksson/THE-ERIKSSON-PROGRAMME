"""Provenance-bearing partial candidate for scaled bulk [35,36]."""

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
SEGMENTS = {
    "35_35p5": (Fraction(35), Fraction(71, 2)),
    "35p5_36": (Fraction(71, 2), Fraction(36)),
}
STEP = Fraction(1, 8)
DEPENDENCIES = (
    "scripts/certify_surface_scaled_bulk_35_36_candidate.py",
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
    parser.add_argument("--unit", choices=tuple(SEGMENTS), required=True)
    args = parser.parse_args()
    lo, hi = SEGMENTS[args.unit]
    ctx.prec = 180
    print("PROVENANCE git_head", head(), flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", flint.__version__, flush=True)
    print("PROVENANCE arb_bits", ctx.prec, flush=True)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(ROOT / relative), flush=True)
    print("CONFIG unit", args.unit, "beta", lo, hi, "step", STEP,
          "CWIN 4 beta_order 12 t_order 9", flush=True)
    scaled.install_design_backend()
    scaled.bulk.CWIN = Fraction(4)
    total = scaled.bulk.cover(lo, hi, db=STEP,
                              prec=180, order=12, t_order=9)
    print("CANDIDATE SCALED BULK UNIT", args.unit,
          "beta_boxes 4 t_boxes", total, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
