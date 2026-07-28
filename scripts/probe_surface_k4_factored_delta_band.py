"""Candidate-only centred-delta K4 band with a factored Taylor weight.

This is an isolated low-z core smoke.  It deliberately excludes the moving
outer band, the global t-union, and all S1'''/S2''' promotion obligations.
"""

from __future__ import annotations

import argparse
import hashlib
import platform
import subprocess
from math import factorial
from pathlib import Path

import flint
from flint import arb, ctx

import surface_remainder_centered_delta_carrier as carrier
from surface_remainder_centered_prefactor_lowz_candidate import outer_derivatives
from surface_remainder_centered_delta_integrator_factored import (
    single_box_fractions,
)
from surface_remainder_scaled_centered_integrator_design import (
    adaptive_scaled_integral,
)


ROOT = Path(__file__).resolve().parents[1]
DEPS = (
    "scripts/probe_surface_k4_factored_delta_band.py",
    "scripts/surface_remainder_centered_delta_integrator_factored.py",
    "scripts/surface_remainder_scaled_centered_integrator_design.py",
    "scripts/surface_remainder_centered_delta_carrier.py",
    "scripts/surface_remainder_centered_prefactor_lowz_candidate.py",
    "scripts/surface_bessel_entire_lowz.py",
    "scripts/surface_remainder_centered_prefactor.py",
    "scripts/surface_remainder_core_l2_arb.py",
    "scripts/surface_remainder_complement.py",
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True,
    ).strip()


def install_lowz_jet() -> None:
    def scaled_bessel_jet(z, family):
        values = outer_derivatives(z.v, family)
        return z._compose([
            value / arb(factorial(order))
            for order, value in enumerate(values)
        ])
    carrier.scaled_bessel_jet = scaled_bessel_jet


def transcript(max_cells: int) -> str:
    ctx.prec = 100
    install_lowz_jet()
    lo, hi = arb("0.0660"), arb("0.0661")
    totals, cells, side = adaptive_scaled_integral(
        lo, hi, t=arb("2.9"), seed_grid=4, max_cells=max_cells)
    fractions = single_box_fractions(totals, lo, hi)
    lines = [
        "SURFACE K4 FACTORED DELTA BAND SMOKE",
        f"git_head {git_head()}",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"config delta {lo.str(24)} {hi.str(24)} t 29/10 seed_grid 4 max_cells {max_cells}",
        f"cells {cells}",
        f"scaled_side {side.str(40)}",
        "weight_formula (hi-lo)*(delta_final-(hi+lo)/2)",
    ]
    for relative in DEPS:
        lines.append(f"dependency {relative} sha256 {sha(ROOT / relative)}")
    for name in sorted(totals):
        lines.append(
            f"row {name} total {totals[name].str(50)} "
            f"fraction {fractions[name].str(40)}"
        )
    lines.extend([
        "CANDIDATE FACTORED DELTA BAND PASS",
        "SCOPE one low-z scaled core band; no outer-band, K4, S1'''/S2''', G2, or G6 promotion",
    ])
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-cells", type=int, default=256)
    args = parser.parse_args()
    output = (ROOT / args.output).resolve()
    output.relative_to(ROOT)
    output.write_text(transcript(args.max_cells), encoding="utf-8", newline="\n")
    print(f"WROTE {output.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
