"""Frozen-unit production engine for the compact G5 extension to beta 25."""

import argparse
from fractions import Fraction
import hashlib
from pathlib import Path
import platform
import subprocess

import flint
from flint import ctx

import certify_bulk_beta_taylor_arb as bulk
import certify_right_edge_beta_taylor_arb as right
import certify_right_edge_beta_taylor_cached_design as cached


ROOT = Path(__file__).resolve().parents[1]
SEGMENTS = {
    "20_22p62": (Fraction(20), Fraction(1131, 50),
                  Fraction(1, 100), Fraction(1, 1000)),
    "22p62_23": (Fraction(1131, 50), Fraction(23),
                  Fraction(1, 100), Fraction(1, 2000)),
    "23_24": (Fraction(23), Fraction(24),
               Fraction(1, 100), Fraction(1, 4000)),
    "24_25": (Fraction(24), Fraction(25),
               Fraction(1, 100), Fraction(1, 4000)),
}
DEPENDENCIES = (
    "scripts/certify_right_edge_beta_taylor_cached_extension.py",
    "scripts/certify_right_edge_beta_taylor_cached_design.py",
    "scripts/certify_right_edge_beta_taylor_arb.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fraction_string(value):
    return f"{value.numerator}/{value.denominator}"


def current_head():
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", choices=tuple(SEGMENTS), required=True)
    args = parser.parse_args()
    lo, hi, step, splice = SEGMENTS[args.unit]
    ctx.prec = 140
    print("PROVENANCE git_head", current_head(), flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", flint.__version__, flush=True)
    print("PROVENANCE arb_bits", ctx.prec, flush=True)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(ROOT/relative), flush=True)
    print("CONFIG unit", args.unit, "beta", fraction_string(lo),
          fraction_string(hi), "step", fraction_string(step), "splice",
          fraction_string(splice), "beta_order 12 d_order 9 CWIN 3/2",
          flush=True)
    cached.install_cached_backend()
    right.SPLICE = splice
    boxes, normalized, regular = right.cover_beta(lo, hi, step)
    print("CERTIFIED RIGHT-EDGE COMPACT EXTENSION UNIT", args.unit,
          "beta_boxes", boxes, "normalized_boxes", normalized,
          "regular_boxes", regular, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
