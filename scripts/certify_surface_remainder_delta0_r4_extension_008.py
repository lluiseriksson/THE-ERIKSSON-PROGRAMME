"""Authoritative regular K2 cover through delta=0.008."""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
from time import perf_counter

import flint
from flint import arb, ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_008_fixed_cover as cover


ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/certify_surface_remainder_delta0_r4_extension_008.py",
    "scripts/surface_remainder_delta0_r4_extension_008_fixed_cover.py",
    "scripts/surface_remainder_delta0_r4_extension_008_cover.py",
    "scripts/surface_remainder_delta0_outer_domain_v5.py",
    "scripts/surface_remainder_delta0_outer_domain_v3.py",
    "scripts/surface_remainder_delta0_outer_domain_v2.py",
    "scripts/surface_remainder_delta0_r4_extension_008_split_probe.py",
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
SEGMENTS = ((0, 13), (13, 25), (25, 38), (38, 50),
            (50, 98), (98, 146), (146, 152), (152, 158))


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def grid_for(index):
    return cover.grid_for(index)


def fraction_string(value):
    return f"{value.numerator}/{value.denominator}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--start-index", type=int, required=True)
    parser.add_argument("--stop-index", type=int, required=True)
    args = parser.parse_args()
    if (args.start_index, args.stop_index) not in SEGMENTS:
        parser.error("segment is not in the frozen production partition")
    boxes = list(regular.sealed.born_t_boxes())
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
    print("CONFIG delta_max 1/125 physical_inner 1181/1000 "
          "band_radius 66/5 core_boxes "
          "0:1/200,1/200:3/500,3/500:7/1000,7/1000:1/125 "
          "annulus_births 0:8 start", args.start_index, "stop",
          args.stop_index, "grid_ranges", cover.GRID_RANGES, flush=True)
    worst = None
    for index in range(args.start_index, args.stop_index):
        lo, hi = boxes[index]
        grid = grid_for(index)
        radius, c4, value, margin = cover.cover.judge_t(lo, hi, grid)
        lower = arb(margin.lower())
        row = {"index": index, "t_lo": fraction_string(lo),
               "t_hi": fraction_string(hi), "grid": grid,
               "band_radius": fraction_string(radius),
               "Y4": c4.str(80), "C_value": value.str(80),
               "margin": margin.str(80), "margin_lower": lower.str(80)}
        print("ROW "+json.dumps(row, sort_keys=True), flush=True)
        if radius != cover.cover.Fraction(66, 5) or not lower > 0:
            print("CERTIFICATE FAIL index", index, flush=True)
            return 1
        if worst is None or lower < worst[0]:
            worst = (lower, index)
    print("CERTIFIED SEGMENT regular K2 r4 delta [0,1/125] start",
          args.start_index, "stop", args.stop_index, "rows",
          args.stop_index-args.start_index, "worst_index", worst[1],
          "worst_margin_lower", worst[0], "elapsed_seconds",
          perf_counter()-started, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
