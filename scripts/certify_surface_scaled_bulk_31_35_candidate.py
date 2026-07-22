"""Provenance-bearing candidate certificate for scaled bulk [31,35]."""

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
    "31_32": (Fraction(31), Fraction(32)),
    "32_33": (Fraction(32), Fraction(33)),
    "33_34": (Fraction(33), Fraction(34)),
    "34_35": (Fraction(34), Fraction(35)),
}
STEP = Fraction(1, 10)
ORDER = 12
T_ORDER = 9
PREC = 180


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def head() -> str:
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def main() -> int:
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", choices=tuple(SEGMENTS), required=True)
    args = parser.parse_args()
    lo, hi = SEGMENTS[args.unit]
    ctx.prec = PREC
    print("PROVENANCE git_head", head(), flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", flint.__version__, flush=True)
    print("PROVENANCE arb_bits", ctx.prec, flush=True)
    dependencies = (
        "scripts/certify_surface_scaled_bulk_31_35_candidate.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
    )
    for relative in dependencies:
        print("DEPENDENCY", relative, sha256(ROOT / relative), flush=True)
    print("CONFIG unit", args.unit, "beta", lo, hi, "step", STEP,
          "CWIN 4 beta_order", ORDER, "t_order", T_ORDER,
          "prec", PREC, flush=True)
    scaled.install_design_backend()
    scaled.bulk.CWIN = Fraction(4)
    total = scaled.bulk.cover(lo, hi, db=STEP,
                              prec=PREC, order=ORDER, t_order=T_ORDER)
    print("PRODUCTION SCALED BULK UNIT", args.unit,
          "beta_boxes 10 t_boxes", total, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
