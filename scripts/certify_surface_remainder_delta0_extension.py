"""Authoritative segmented cover of the regular K2 lane [0,1/250]."""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
from time import perf_counter

import flint
from flint import arb, ctx

import surface_remainder_delta0_extension_cover as design
import surface_remainder_delta0_extension_probe as probe


ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/certify_surface_remainder_delta0_extension.py",
    "scripts/surface_remainder_delta0_extension_cover.py",
    "scripts/surface_remainder_delta0_extension_probe.py",
    "scripts/surface_remainder_delta0_series_cover_design.py",
    "scripts/surface_remainder_delta0_series_design.py",
    "scripts/surface_remainder_delta0_companion_error.py",
    "scripts/surface_remainder_delta0_derivative_tail.py",
    "scripts/surface_remainder_s2_direct_judge.py",
    "scripts/surface_bessel_integral_remainder.py",
)
GRID_RANGES = (
    (0, 44, 192),
    (45, 135, 384),
    (136, 151, 768),
    (152, 154, 1024),
    (155, 156, 1536),
    (157, 157, 1024),
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def grid_for(index):
    matches = [grid for lo, hi, grid in GRID_RANGES if lo <= index <= hi]
    if len(matches) != 1:
        raise ValueError("production grid map is not a partition")
    return matches[0]


def fraction_string(value):
    return f"{value.numerator}/{value.denominator}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--start-index", type=int, required=True)
    parser.add_argument("--stop-index", type=int, required=True)
    args = parser.parse_args()
    boxes = list(probe.sealed.born_t_boxes())
    if not 0 <= args.start_index < args.stop_index <= len(boxes):
        parser.error("invalid half-open segment")
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
    print("CONFIG delta_max 1/250 start", args.start_index, "stop",
          args.stop_index, "grid_ranges", GRID_RANGES, flush=True)
    worst = None
    for index in range(args.start_index, args.stop_index):
        lo, hi = boxes[index]
        grid = grid_for(index)
        c3, value, margin = probe.judge(
            design.DELTA_MAX, lo, hi, grid, parallel=True)
        lower = arb(margin.lower())
        row = {
            "index": index,
            "t_lo": fraction_string(lo),
            "t_hi": fraction_string(hi),
            "grid": grid,
            "Y3": c3.str(80),
            "C_value": value.str(80),
            "margin": margin.str(80),
            "margin_lower": lower.str(80),
        }
        print("ROW "+json.dumps(row, sort_keys=True), flush=True)
        if not lower > 0:
            print("CERTIFICATE FAIL index", index, flush=True)
            return 1
        if worst is None or lower < worst[0]:
            worst = (lower, index)
    print("CERTIFIED SEGMENT regular K2 delta [0,1/250] start",
          args.start_index, "stop", args.stop_index, "rows",
          args.stop_index-args.start_index, "worst_index", worst[1],
          "worst_margin_lower", worst[0], "elapsed_seconds",
          perf_counter()-started, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
