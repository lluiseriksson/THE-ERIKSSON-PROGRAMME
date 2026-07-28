"""Degree-eight centered complex-circle probe for the nominal K2 square."""

from __future__ import annotations

from pathlib import Path

from flint import arb, ctx

import probe_surface_k2_fixed_square_centered_complex_supremum as centered
import probe_surface_k2_fixed_square_complex_supremum as base
from surface_remainder_delta0_exact_targets import (
    target_y3,
    target_y4,
    target_y5,
    target_y6,
    target_y7,
)
from surface_remainder_s2_direct_judge import closed_forms


ROOT = Path(__file__).resolve().parents[1]
PRODUCTION = (
    ROOT/"outputs"/
    "surface-r7-r8-sparse-exact-target-production-20260728.txt"
)
REPLAY = (
    ROOT/"outputs"/
    "surface-r7-r8-sparse-exact-target-replay-20260728.txt"
)
PASS_TOKEN = "R7/R8 SPARSE EXACT TARGET CHECK PASS"
LADDER = ((48, 64), (96, 128))
COMPANION_ORDER = 8


def mathematical_lines(text):
    return [
        line for line in text.splitlines()
        if line.startswith("Y") and len(line) > 1 and line[1].isdigit()
    ]


def require_exact_head_certificates(
    production=PRODUCTION,
    replay=REPLAY,
):
    production_text = Path(production).read_text(encoding="utf-8")
    replay_text = Path(replay).read_text(encoding="utf-8")
    if PASS_TOKEN not in production_text or PASS_TOKEN not in replay_text:
        raise RuntimeError("R7/R8 exact-head production/replay not green")
    production_math = mathematical_lines(production_text)
    replay_math = mathematical_lines(replay_text)
    if len(production_math) != 8 or production_math != replay_math:
        raise RuntimeError("R7/R8 exact-head replay mismatch")
    return production_math


def cauchy_budget():
    _, _, y2, theta3 = closed_forms(base.T)
    c = (base.T/4).cos()
    heads = [
        y2,
        target_y3(c),
        target_y4(c),
        target_y5(c),
        target_y6(c),
        target_y7(c),
    ]
    retained = sum(
        (
            heads[order-2]*base.DELTA_MAX**(order-2)
            for order in range(2, 8)
        ),
        arb(0),
    )
    available = (
        theta3-arb(retained.abs_upper())
    )*base.DELTA_MAX**2
    q = base.DELTA_MAX/base.RHO
    multiplier = q**8/(1-q)
    return retained, available, multiplier, available/multiplier


def main():
    ctx.prec = 140
    require_exact_head_certificates()
    base.COMPANION_ORDER = COMPANION_ORDER
    retained, available, multiplier, required_m = cauchy_budget()
    print("K2 R8 CENTERED COMPLEX SUPREMUM DESIGN", flush=True)
    print("rho", base.RHO, "delta_max", base.DELTA_MAX, flush=True)
    print("companion_order", COMPANION_ORDER, flush=True)
    print("retained_Y2_through_Y7", retained, flush=True)
    print("available_remainder", available, flush=True)
    print("cauchy_multiplier", multiplier, flush=True)
    print("required_M", required_m, flush=True)
    passed = False
    for grid, theta_count in LADDER:
        try:
            mass_floor, worst = centered.run(grid, theta_count)
        except (ValueError, ZeroDivisionError) as exc:
            print(
                "LEVEL",
                grid,
                theta_count,
                "UNRESOLVED",
                type(exc).__name__,
                str(exc),
                flush=True,
            )
            continue
        passed = (
            arb(mass_floor.lower()) > 0
            and worst.is_finite()
            and arb(worst.upper()) < required_m
        )
        print(
            "LEVEL",
            grid,
            theta_count,
            "MASS_FLOOR",
            mass_floor,
            "M_SUP",
            worst,
            "PASS",
            passed,
            flush=True,
        )
        if passed:
            break
    print(
        "K2 R8 CENTERED COMPLEX SUPREMUM DESIGN "
        + ("PASS" if passed else "FAIL")
        + "; TRUE COMPANION AND EXTERIOR OPEN",
        flush=True,
    )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
