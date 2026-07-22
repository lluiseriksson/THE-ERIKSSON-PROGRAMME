"""Candidate signed-bilinear endpoint cover for the K2 remainder.

This driver retains the cellwise cancellation
``KD*HDF-KF*HDD`` before summation, then adds the registered outer-derivative
charges and the order-five Bessel companion value charge.  It is deliberately
labelled candidate-only: it does not alter the terminal K2 certificate or the
G2 relay until an independent claim audit accepts the exact accounting.
"""

from __future__ import annotations

import argparse
import hashlib
import platform
import subprocess
from pathlib import Path

from flint import arb, ctx

from probe_surface_remainder_signed_bilinear_with_tails import charged_series
from probe_surface_remainder_signed_bilinear_series import quotient_y3
from surface_remainder_arb_jet2 import hull
from surface_remainder_companion_error_ordered import (
    normalized_y_error_coefficient,
)
from surface_remainder_delta0_series_cover_design import born_t_boxes
from surface_remainder_s2_direct_judge import closed_forms


ROOT = Path(__file__).resolve().parents[1]
DELTA_MAX = arb(1) / 1000
DEPS = (
    "scripts/certify_surface_remainder_signed_bilinear_endpoint_candidate.py",
    "scripts/probe_surface_remainder_signed_bilinear_with_tails.py",
    "scripts/probe_surface_remainder_signed_bilinear_series.py",
    "scripts/surface_remainder_delta0_series_design.py",
    "scripts/surface_remainder_delta0_derivative_tail.py",
    "scripts/surface_remainder_companion_error_ordered.py",
    "scripts/surface_bessel_integral_remainder.py",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_head() -> str:
    result = subprocess.run(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"],
        cwd=ROOT, text=True, capture_output=True, check=True,
    )
    return result.stdout.strip()


def judge(lo, hi, grid: int):
    t = hull(arb(lo.numerator) / arb(lo.denominator),
             arb(hi.numerator) / arb(hi.denominator))
    base = hull(arb(0), DELTA_MAX)
    bilinear, kd, _ = charged_series(t, base, grid)
    q3 = quotient_y3(bilinear, kd, t)
    _, _, r3, theta3 = closed_forms(t)
    slack = theta3 - arb(r3.abs_upper())
    kd_lower = arb(kd.coeffs()[0].lower())
    if not kd_lower > 0:
        raise RuntimeError(f"nonpositive KD lower on [{lo},{hi}]")
    # The order-five companion error is O(delta^5) in Y.  After the exact
    # r3 head is charged, this contributes C5*delta^3 to the coefficient
    # budget (the legacy order-four route used C4*delta^2).
    c5 = normalized_y_error_coefficient(
        DELTA_MAX, kd_lower, arb(10), order=5)
    margin = slack - arb(q3.rad().upper()) * DELTA_MAX - c5 * DELTA_MAX**3
    return q3, c5, margin, kd_lower


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=None,
                        help="only run the first N born t boxes (smoke)")
    parser.add_argument("--grid", type=int, default=96)
    args = parser.parse_args()
    if args.grid <= 0:
        raise ValueError("grid must be positive")
    ctx.prec = 140
    boxes = list(born_t_boxes())
    if args.limit is not None:
        boxes = boxes[:args.limit]
    lines = [
        "SIGNED BILINEAR K2 ENDPOINT CANDIDATE",
        f"PROVENANCE git_head {git_head()}",
        f"PROVENANCE python {platform.python_version()}",
        "PROVENANCE python_flint 0.9.0",
        "PROVENANCE arb_bits 140",
        f"CONFIG delta=[0,1/1000] grid={args.grid} order5_companion=true",
    ]
    for rel in DEPS:
        lines.append(f"DEPENDENCY {rel} {digest(ROOT / rel)}")
    passed = 0
    worst = None
    for lo, hi in boxes:
        q3, c5, margin, kd_lower = judge(lo, hi, args.grid)
        lower = arb(margin.lower())
        if lower <= 0:
            raise RuntimeError(
                f"nonpositive candidate margin on [{lo},{hi}]: {margin}")
        passed += 1
        if worst is None or lower < worst:
            worst = lower
        lines.append(
            "ROW [%s,%s] grid=%d Y3_radius=%s C5=%s KD0_lower=%s "
            "margin_lower=%s" % (
                lo, hi, args.grid, q3.rad().str(18), c5.str(18),
                kd_lower.str(18), margin.str(18)))
    lines.extend([
        f"COVERAGE boxes={len(boxes)} passed={passed}",
        f"WORST_MARGIN_LOWER {worst.str(30) if worst is not None else 'none'}",
        "CANDIDATE PASS; signed cancellation and order-five companion only",
        "SCOPE no K2/G2/G6/S1'''/S2''' promotion",
    ])
    output = (ROOT / args.output).resolve()
    output.relative_to(ROOT)
    output.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print("SIGNED BILINEAR ENDPOINT CANDIDATE PASS", output.relative_to(ROOT))
    print("SCOPE candidate only; no K2/G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
