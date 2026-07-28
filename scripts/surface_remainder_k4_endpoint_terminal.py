"""One-box K4 endpoint certificate (explicitly not a global union)."""

import hashlib
from pathlib import Path
import platform
import subprocess
from time import perf_counter

import flint
from flint import arb, ctx

import surface_remainder_centered_delta_integrator_design as design


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT / "scripts" / "surface_remainder_k4_endpoint_terminal_transcript.txt"
DEPENDENCIES = (
    "scripts/surface_remainder_k4_endpoint_terminal.py",
    "scripts/surface_remainder_centered_delta_integrator_design.py",
    "scripts/surface_remainder_centered_delta_carrier.py",
    "scripts/surface_remainder_complement_l3_smoke.py",
    "scripts/surface_remainder_tjet.py",
    "scripts/surface_remainder_complement.py",
    "scripts/surface_bessel_integral_remainder.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_head():
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def main():
    ctx.prec = 140
    started = perf_counter()
    lo, hi = arb("0.049"), arb("0.05")
    totals, cells, fallbacks = design.adaptive_integral(
        lo, hi, max_cells=1152)
    fractions = design.single_box_fractions(totals, lo, hi)
    lines = [
        "K4 ENDPOINT ONE-BOX TERMINAL",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {current_head()}",
        "box delta 0.049 0.05",
        f"cells {cells} fallbacks {fallbacks}",
    ]
    for relative in DEPENDENCIES:
        lines.append(f"dependency {relative} sha256 {sha256(ROOT/relative)}")
    for name in design.BUDGETS:
        lines.append(f"fraction {name} {fractions[name].str(80)}")
    passed = cells == 1152 and all(
        totals[name].is_finite() and fractions[name] < 1
        for name in design.BUDGETS)
    lines.append("K4 ENDPOINT ONE-BOX PASS" if passed
                 else "K4 ENDPOINT ONE-BOX FAIL")
    lines.append(f"elapsed_seconds {perf_counter()-started}")
    lines.append("SCOPE one positive delta box only; no K4 union or theorem claim")
    TRANSCRIPT.write_text("\n".join(lines)+"\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
