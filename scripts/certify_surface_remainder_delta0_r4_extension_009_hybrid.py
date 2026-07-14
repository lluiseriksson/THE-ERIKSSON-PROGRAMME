"""Authoritative one-unit regular-K2 production for the ninth-birth hybrid."""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
from time import perf_counter

import flint
from flint import arb, ctx

import surface_remainder_delta0_r4_extension_009_hybrid_contract as hybrid
import surface_remainder_delta0_r4_extension_009_fixed_cover as fixed


ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/certify_surface_remainder_delta0_r4_extension_009_hybrid.py",
    "scripts/surface_remainder_delta0_r4_extension_009_hybrid_contract.py",
    "scripts/surface_remainder_delta0_r4_extension_009_fixed_cover.py",
    "scripts/surface_remainder_delta0_r4_extension_009_cover.py",
    "scripts/surface_remainder_delta0_band_gap_design.py",
    "scripts/surface_remainder_delta0_tlocal_band_design.py",
    "scripts/surface_remainder_delta0_outer_domain_v6.py",
    "scripts/surface_remainder_delta0_outer_domain_v5.py",
    "scripts/surface_remainder_delta0_outer_domain_v3.py",
    "scripts/surface_remainder_delta0_outer_domain_v2.py",
    "scripts/surface_remainder_delta0_r4_extension_009_split_probe.py",
    "scripts/surface_remainder_delta0_r4_extension_probe.py",
    "scripts/surface_remainder_delta0_extension_probe.py",
    "scripts/surface_remainder_delta0_series_cover_design.py",
    "scripts/surface_remainder_delta0_series_design.py",
    "scripts/surface_remainder_delta0_companion_error.py",
    "scripts/surface_remainder_delta0_derivative_tail.py",
    "scripts/surface_remainder_delta0_fourth_coefficient.py",
    "scripts/surface_remainder_s2_direct_judge.py",
    "scripts/surface_bessel_integral_remainder.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fraction_string(value):
    return f"{value.numerator}/{value.denominator}"


def unit_map():
    return {unit.slug: unit for unit in hybrid.regular_units()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", choices=tuple(unit_map()), required=True)
    args = parser.parse_args()
    unit = unit_map()[args.unit]
    ctx.prec = 140
    started = perf_counter()
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    print("PROVENANCE git_head", head, flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", flint.__version__, flush=True)
    print("PROVENANCE arb_bits", ctx.prec, flush=True)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(ROOT/relative), flush=True)
    print(
        "CONFIG delta_birth 1/125:9/1000 regular_t 0:313/100 "
        "moving_edge_C 3/2 physical_inner 1181/1000 band_radius 62/5 "
        "unit",
        unit.slug,
        flush=True,
    )
    radius, c4, value, margin = fixed.cover.judge_t(
        unit.lo, unit.hi, unit.grid)
    lower = arb(margin.lower())
    row = {
        "slug": unit.slug,
        "kind": unit.kind,
        "index": unit.index,
        "depth": unit.depth,
        "part": unit.part,
        "t_lo": fraction_string(unit.lo),
        "t_hi": fraction_string(unit.hi),
        "grid": unit.grid,
        "band_radius": fraction_string(radius),
        "Y4": c4.str(80),
        "C_value": value.str(80),
        "margin": margin.str(80),
        "margin_lower": lower.str(80),
    }
    print("ROW " + json.dumps(row, sort_keys=True), flush=True)
    if radius != fixed.cover.Fraction(62, 5) or not lower > 0:
        print("CERTIFICATE FAIL unit", unit.slug, flush=True)
        return 1
    print(
        "CERTIFIED UNIT regular K2 r4 hybrid009",
        unit.slug,
        "elapsed_seconds",
        perf_counter() - started,
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
