"""Two-box K4 weighted endpoint strip (local t stress only)."""

import hashlib
from pathlib import Path
import platform
import subprocess
from time import perf_counter

import flint
from flint import arb, ctx

import surface_remainder_centered_delta_integrator_design as design


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT / "scripts" / "surface_remainder_k4_endpoint_strip_transcript.txt"
DEPENDENCIES = (
    "scripts/surface_remainder_k4_endpoint_strip_terminal.py",
    "scripts/surface_remainder_centered_delta_integrator_design.py",
    "scripts/surface_remainder_centered_delta_carrier.py",
    "scripts/surface_remainder_complement_l3_smoke.py",
    "scripts/surface_remainder_tjet.py",
    "scripts/surface_remainder_complement.py",
    "scripts/surface_bessel_integral_remainder.py",
)
SEGMENTS = (("0.048", "0.049", 2304), ("0.049", "0.05", 1152))


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_head():
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def main():
    ctx.prec = 140
    started = perf_counter()
    totals = {name: arb(0) for name in design.BUDGETS}
    lines = [
        "K4 ENDPOINT TWO-BOX STRIP TERMINAL",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {current_head()}",
        "t_stress 2.9",
    ]
    for index, (lo_text, hi_text, max_cells) in enumerate(SEGMENTS):
        lo, hi = arb(lo_text), arb(hi_text)
        segment, cells, fallbacks = design.adaptive_integral(
            lo, hi, t=arb("2.9"), max_cells=max_cells)
        fractions = design.single_box_fractions(segment, lo, hi)
        lines.append(
            f"segment {index} delta {lo_text} {hi_text} cells {cells} "
            f"fallbacks {fallbacks}")
        for name in design.BUDGETS:
            totals[name] += fractions[name]
            lines.append(f"segment_fraction {index} {name} "
                         f"{fractions[name].str(80)}")
    for relative in DEPENDENCIES:
        lines.append(f"dependency {relative} sha256 {sha256(ROOT/relative)}")
    passed = all(value.is_finite() and value < 1 for value in totals.values())
    for name, value in totals.items():
        lines.append(f"total_fraction {name} {value.str(80)}")
    lines.append("K4 ENDPOINT TWO-BOX STRIP PASS" if passed
                 else "K4 ENDPOINT TWO-BOX STRIP FAIL")
    lines.append(f"elapsed_seconds {perf_counter()-started}")
    lines.append("SCOPE t=2.9 only; delta [0.048,0.05]; no global K4 theorem claim")
    TRANSCRIPT.write_text("\n".join(lines)+"\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())

