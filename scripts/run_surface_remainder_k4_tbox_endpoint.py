"""Run one explicit K4 endpoint t-box on the fixed two-box delta strip.

The driver is scoped evidence only.  It never asserts a global K4 theorem or
the S1'''/S2''' relay; each invocation records its exact t-box and dependencies.
"""

import argparse
import hashlib
from pathlib import Path
import platform
import subprocess

import flint
from flint import arb, ctx

import surface_remainder_centered_delta_integrator_design as design

ROOT = Path(__file__).resolve().parents[1]
SEGMENTS = (("0.048", "0.049", 2304), ("0.049", "0.05", 1152))


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_head():
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def run(unit, t_lo_text, t_hi_text):
    ctx.prec = 140
    t = design.hull(arb(t_lo_text), arb(t_hi_text))
    totals = {name: arb(0) for name in design.BUDGETS}
    lines = [
        f"K4 ENDPOINT TBOX {unit}",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {current_head()}",
        f"t_domain {t_lo_text} {t_hi_text} {t.str(40)}",
    ]
    for index, (lo_text, hi_text, max_cells) in enumerate(SEGMENTS):
        lo, hi = arb(lo_text), arb(hi_text)
        segment, cells, fallbacks = design.adaptive_integral(
            lo, hi, t=t, max_cells=max_cells)
        fractions = design.single_box_fractions(segment, lo, hi)
        lines.append(
            f"segment {index} delta {lo_text} {hi_text} cells {cells} "
            f"fallbacks {fallbacks}")
        for name in design.BUDGETS:
            totals[name] += fractions[name]
            lines.append(f"segment_fraction {index} {name} "
                         f"{fractions[name].str(80)}")
    dependencies = (
        "scripts/run_surface_remainder_k4_tbox_endpoint.py",
        "scripts/surface_remainder_centered_delta_integrator_design.py",
        "scripts/surface_remainder_centered_delta_carrier.py",
        "scripts/surface_remainder_complement_l3_smoke.py",
        "scripts/surface_remainder_tjet.py",
        "scripts/surface_remainder_complement.py",
        "scripts/surface_bessel_integral_remainder.py",
    )
    for relative in dependencies:
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    passed = all(value.is_finite() and value.upper() < 1
                 for value in totals.values())
    for name, value in totals.items():
        lines.append(f"total_fraction {name} {value.str(80)}")
    lines.append(f"K4 ENDPOINT TBOX {unit} " + ("PASS" if passed else "FAIL"))
    lines.append(
        f"SCOPE t=[{t_lo_text},{t_hi_text}] only; delta [0.048,0.05]; "
        "no global K4 theorem claim")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--t-lo", required=True)
    parser.add_argument("--t-hi", required=True)
    args = parser.parse_args()
    print(run(args.unit, args.t_lo, args.t_hi), end="")
