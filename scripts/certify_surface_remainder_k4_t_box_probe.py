"""Candidate-only K4 fixed delta/t box transcript driver.

This reuses the frozen centred-delta cell evaluator but keeps a rational
whole-t interval in every Arb call.  It is deliberately separate from the
manifested t=2.9 band driver: changing the latter would invalidate its old
provenance.  No gate is promoted by this script.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, ctx

import certify_surface_remainder_k4_centered_band as frozen
from surface_remainder_arb_jet2 import hull


ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def q(value: str) -> Fraction:
    return Fraction(value)


def run(args) -> str:
    dlo, dhi = q(args.delta_lo), q(args.delta_hi)
    tlo, thi = q(args.t_lo), q(args.t_hi)
    if not (0 < dlo < dhi and tlo < thi):
        raise ValueError("ordered positive delta/t boxes required")
    ctx.prec = args.precision
    # The frozen evaluator reads its t parameter from this module global.
    frozen.T = hull(arb(tlo.numerator)/tlo.denominator,
                    arb(thi.numerator)/thi.denominator)
    cells = frozen.terminal_cells(
        arb(dlo.numerator)/dlo.denominator,
        arb(dhi.numerator)/dhi.denominator,
        args.max_cells,
    )
    totals = {name: arb(0) for name in frozen.NAMES}
    fallbacks = 0
    for *_, values, fallback in cells:
        fallbacks += int(fallback)
        for name in frozen.NAMES:
            totals[name] += values[name]
    fractions = frozen.design.single_box_fractions(
        totals, arb(dlo.numerator)/dlo.denominator,
        arb(dhi.numerator)/dhi.denominator)
    passed = frozen.design.fractions_pass(fractions)
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT, text=True,
    ).strip()
    lines = [
        "K4 CENTERED T-BOX PROBE TRANSCRIPT",
        f"PROVENANCE git_head {head}",
        f"PROVENANCE python {platform.python_version()}",
        f"PROVENANCE python_flint {flint.__version__}",
        f"PROVENANCE arb_bits {ctx.prec}",
        (f"CONFIG delta {dlo}:{dhi} t {tlo}:{thi} seed_grid "
         f"{frozen.SEED_GRID} max_cells {args.max_cells} precision {args.precision}"),
    ]
    for relative in (
        "scripts/certify_surface_remainder_k4_t_box_probe.py",
        "scripts/certify_surface_remainder_k4_centered_band.py",
        "scripts/surface_remainder_centered_delta_integrator_design.py",
        "scripts/surface_remainder_centered_delta_carrier.py",
        "scripts/surface_remainder_complement_l3_smoke.py",
        "scripts/surface_remainder_complement.py",
    ):
        lines.append(f"DEPENDENCY {relative} {sha256(ROOT / relative)}")
    for index, (_, _, slo, shi, alo, ahi, values, fallback) in enumerate(cells):
        payload = {
            "index": index,
            "s_lo": arb(slo).str(50), "s_hi": arb(shi).str(50),
            "a_lo": arb(alo).str(50), "a_hi": arb(ahi).str(50),
            "fallback": bool(fallback),
            "values": {name: values[name].str(80) for name in frozen.NAMES},
        }
        lines.append("CELL " + json.dumps(payload, sort_keys=True))
    lines.extend([
        f"FALLBACKS {fallbacks}",
        "TOTAL " + json.dumps({name: totals[name].str(80)
                                for name in frozen.NAMES}, sort_keys=True),
        "FRACTIONS " + json.dumps({name: fractions[name].str(80)
                                    for name in frozen.NAMES}, sort_keys=True),
        f"CELLS {len(cells)}",
        "K4 CENTERED T-BOX PROBE " + ("PASS" if passed else "FAIL"),
        "SCOPE candidate t-box only; no K4/S1'''/S2'''/G6 promotion",
    ])
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--delta-lo", required=True)
    parser.add_argument("--delta-hi", required=True)
    parser.add_argument("--t-lo", required=True)
    parser.add_argument("--t-hi", required=True)
    parser.add_argument("--max-cells", type=int, default=9216)
    parser.add_argument("--precision", type=int, default=140)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = (ROOT / args.output).resolve()
    output.relative_to(ROOT)
    transcript = run(args)
    output.write_text(transcript, encoding="utf-8")
    passed = "\nK4 CENTERED T-BOX PROBE PASS\n" in transcript
    print("K4 T-BOX PROBE " + ("PASS" if passed else "FAIL"),
          output.relative_to(ROOT))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
