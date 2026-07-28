"""Authoritative Arb cover of the K2 endpoint lane [0,1/1000]."""

import hashlib
from pathlib import Path
import platform
import subprocess

import flint
from flint import arb, ctx

import surface_remainder_delta0_series_cover_design as cover_module


DEPENDENCIES = (
    "scripts/surface_remainder_delta0_series_cover_design.py",
    "scripts/surface_remainder_delta0_series_design.py",
    "scripts/surface_remainder_delta0_companion_error.py",
    "scripts/surface_remainder_delta0_derivative_tail.py",
    "scripts/surface_remainder_s2_direct_judge.py",
    "scripts/surface_bessel_integral_remainder.py",
)


def provenance():
    path = Path(__file__).resolve()
    root = path.parents[1]
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    out = {
        "script": "scripts/"+path.name,
        "script_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "git_head": head,
        "python": platform.python_version(),
        "python_flint": getattr(flint, "__version__", "UNKNOWN"),
        "arb_prec_bits": "140",
    }
    for dependency in DEPENDENCIES:
        key = Path(dependency).stem+"_sha256"
        out[key] = hashlib.sha256((root/dependency).read_bytes()).hexdigest()
    return out


def certify():
    ctx.prec = 140
    for key, value in provenance().items():
        print("PROVENANCE %s=%s" % (key, value), flush=True)
    print("CONFIG delta=[0,1/1000] t_birth_width=1/50 "
          "grids=96,192 physical_band=1 radial_tail=32", flush=True)
    boxes = list(cover_module.born_t_boxes())
    refined = 0
    for lo, hi in boxes:
        grid, coefficient3, value_charge, margin = \
            cover_module.judge_box(lo, hi)
        refined += int(grid > 96)
        print("t-box [%s,%s]: grid=%d Y3_abs<=%s "
              "C_value<=%s margin_lower=%s margin_ball=%s" %
              (float(lo), float(hi), grid, coefficient3.str(10),
               value_charge.str(10), arb(margin.lower()).str(10),
               margin.str(10)), flush=True)
    print("CERTIFIED (K2 endpoint, Arb): "
          "abs(Y-T-r2*delta)<=Theta3*delta^2 on "
          "[0,1/1000] x [0,pi]; t_boxes=%d refined_grid_boxes=%d" %
          (len(boxes), refined), flush=True)
    return len(boxes), refined


if __name__ == "__main__":
    certify()
