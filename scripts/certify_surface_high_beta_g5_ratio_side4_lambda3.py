"""Authoritative G5 ratio units on 2<=lambda<=3 with |q|<=4."""

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

import surface_right_edge_five_family_beta20_design as beta20
import surface_right_edge_five_family_central_design as central
import surface_right_edge_five_family_finite_tail_design as finite_tail
import surface_right_edge_five_family_tail_design as halfline_tail
from surface_remainder_arb_jet2 import hull
from surface_right_edge_five_family_ratio_design import assemble_ratio


ROOT = Path(__file__).resolve().parents[1]
SIDE = arb(4)
UNITS = tuple((start, start + 5) for start in range(100, 150, 5))
DEPENDENCIES = (
    "scripts/certify_surface_high_beta_g5_ratio_side4_lambda3.py",
    "scripts/surface_right_edge_five_family_ratio_design.py",
    "scripts/surface_right_edge_five_family_central_design.py",
    "scripts/surface_right_edge_five_family_finite_tail_design.py",
    "scripts/surface_right_edge_five_family_beta20_design.py",
    "scripts/surface_right_edge_five_family_tail_design.py",
    "scripts/surface_bessel_integral_remainder.py",
    "scripts/surface_right_edge_scaled_paired_design.py",
    "scripts/surface_remainder_arb_jet2.py",
    "docs/SURFACE-HIGH-BETA-G5-RATIO-SIDE4-LAMBDA3-PREREG-20260728.md",
)


def aq(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def sha256(relative: str) -> str:
    return hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()


def current_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()


def endpoint(value: arb, lower: bool) -> str:
    bound = value.lower() if lower else value.upper()
    return arb(bound).str(80)


def unit_slug(unit: tuple[int, int]) -> str:
    return f"lambda_{unit[0]:03d}_{unit[1]:03d}"


def unit_map() -> dict[str, tuple[int, int]]:
    return {unit_slug(unit): unit for unit in UNITS}


def near_bounds(delta_max: arb, lambda_hi: arb):
    saved = central.reduced_values
    central.reduced_values = finite_tail.low_argument_companion
    try:
        delta = hull(arb(0), delta_max)
        v = hull(finite_tail.VMIN, arb(2))
        i0, i1 = finite_tail.low_argument_companion(delta / v, v)
        gaussian = (
            4
            * lambda_hi.exp()
            * halfline_tail.gaussian_one_side(arb(4) / 3, SIDE)
        )
        u, b = {}, {}
        for order, weight in (
            (1, 2 / arb.pi()),
            (3, 1 / (3 * arb.pi())),
            (5, 1 / (30 * arb.pi())),
        ):
            u[order] = (
                gaussian
                * weight
                * arb(i1.abs_upper())
                * arb(
                    finite_tail.chain(
                        "I1", order, delta_max=delta_max
                    ).abs_upper()
                )
                / 4
            )
        for order, weight in (
            (2, 1 / arb.pi()),
            (4, 2 / (3 * arb.pi())),
        ):
            b[order] = (
                gaussian
                * weight
                * arb(i0.abs_upper())
                * arb(
                    finite_tail.chain(
                        "I0", order, arb(1) / 2, delta_max=delta_max
                    ).abs_upper()
                )
            )
        return u, b
    finally:
        central.reduced_values = saved


def budgets(delta_max: arb, lambda_hi: arb):
    near_u, near_b = near_bounds(delta_max, lambda_hi)
    far_u, far_b = finite_tail.far_bounds(delta_max)
    return (
        near_u[1] + far_u[1],
        near_u[3] + far_u[3],
        near_u[5] + far_u[5],
        near_b[2] + far_b[2],
        near_b[4] + far_b[4],
    )


def install_backend(delta_max: arb, lambda_hi: arb) -> None:
    beta20.install(delta_max)
    endpoint_delta = arb(delta_max.upper())
    angle = (
        arb.pi() / 4
        - SIDE * endpoint_delta.sqrt()
        - lambda_hi * endpoint_delta / 4
    )
    value_floor = 2 * angle.sin()
    if not value_floor > 0:
        raise AssertionError("side-four Bessel value floor is unresolved")
    beta20.ACTIVE_VALUE_FLOOR = value_floor
    beta20.ACTIVE_INVZ_CEILING = endpoint_delta / value_floor
    if not beta20.ACTIVE_INVZ_CEILING < arb(1) / 4:
        raise AssertionError("side-four inverse-z ceiling is unresolved")


def verify_geometry() -> None:
    delta = aq(Fraction(9, 1000))
    shift = aq(Fraction(27, 2000))
    alpha = arb(7) / 50
    assert SIDE * delta.sqrt() < arb.pi() / 4 - alpha - shift / 2
    assert 2 * (alpha - shift).sin() > finite_tail.VMIN
    amplitude = (2 - 2 * shift.sin()).sqrt()
    sinc_floor = 1 - delta * SIDE**2 / 24
    assert amplitude * sinc_floor**2 > arb(4) / 3
    assert delta / finite_tail.VMIN < arb(1) / 4
    finite_tail.verify_geometry()


def judge(delta_index: int, lambda_index: int):
    if not 0 <= delta_index < 9:
        raise ValueError("delta index outside 0..8")
    if not 100 <= lambda_index < 150:
        raise ValueError("lambda index outside 100..149")
    dlo = Fraction(delta_index, 1000)
    dhi = Fraction(delta_index + 1, 1000)
    llo = Fraction(lambda_index, 50)
    lhi = Fraction(lambda_index + 1, 50)
    delta = hull(aq(dlo), aq(dhi))
    lam = hull(aq(llo), aq(lhi))
    install_backend(aq(dhi), aq(lhi))
    charges = budgets(aq(dhi), aq(lhi))

    def enlarge(row):
        return tuple(
            value + charge * arb("0 +/- 1")
            for value, charge in zip(row, charges)
        )

    families = enlarge(
        central.central_families(
            delta, lam, side=SIDE, qgrid=128, rgrid=16,
            thetagrid=4, phigrid=4,
        )
    )
    ratio, ratio_b0 = assemble_ratio(delta, lam, families)
    assert ratio_b0.overlaps(families[3])
    if families[3].lower() > 0 and ratio.lower() > 0:
        return "coarse-ratio", charges, families, ratio

    families = enlarge(
        (
            central.integrate_u_family(
                delta, lam, 1, side=SIDE, qgrid=256, rgrid=32,
                thetagrid=4, phigrid=1,
            ),
            central.integrate_u_family(
                delta, lam, 3, side=SIDE, qgrid=256, rgrid=32,
                thetagrid=8, phigrid=1,
            ),
            central.integrate_u_family(
                delta, lam, 5, side=SIDE, qgrid=256, rgrid=32,
                thetagrid=4, phigrid=1,
            ),
            central.integrate_b_family(
                delta, lam, 2, side=SIDE, qgrid=256, rgrid=32,
                thetagrid=1,
            ),
            central.integrate_b_family(
                delta, lam, 4, side=SIDE, qgrid=256, rgrid=32,
                thetagrid=8,
            ),
        )
    )
    ratio, ratio_b0 = assemble_ratio(delta, lam, families)
    assert ratio_b0.overlaps(families[3])
    return "mixed-ratio", charges, families, ratio


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", choices=tuple(unit_map()), required=True)
    args = parser.parse_args()
    unit = unit_map()[args.unit]
    ctx.prec = 140
    verify_geometry()
    print("HIGH-BETA G5 RATIO SIDE4 LAMBDA3 UNIT", args.unit, flush=True)
    print("PROVENANCE git_head", current_head(), flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", flint.__version__, flush=True)
    print("PROVENANCE arb_bits", ctx.prec, flush=True)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(relative), flush=True)
    print(
        "CONFIG delta_partition 0:9/1000:1/1000 "
        f"lambda_unit {unit[0]}/50:{unit[1]}/50:1/50 "
        "lambda_max 3 side 4 near_exp exp(lambda_hi) "
        "coarse qgrid128 rgrid16 mixed qgrid256 rgrid32",
        flush=True,
    )
    rows = 0
    worst = None
    for lambda_index in range(*unit):
        for delta_index in range(9):
            resolution, charges, families, ratio = judge(
                delta_index, lambda_index
            )
            row = {
                "delta_index": delta_index,
                "delta_lo": f"{delta_index}/1000",
                "delta_hi": f"{delta_index + 1}/1000",
                "lambda_index": lambda_index,
                "lambda_lo": f"{lambda_index}/50",
                "lambda_hi": f"{lambda_index + 1}/50",
                "resolution": resolution,
                "tail_budgets": [
                    endpoint(value, False) for value in charges
                ],
                "B0_lower": endpoint(families[3], True),
                "B0_upper": endpoint(families[3], False),
                "Qratio_lower": endpoint(ratio, True),
                "Qratio_upper": endpoint(ratio, False),
            }
            print("ROW " + json.dumps(row, sort_keys=True), flush=True)
            b0_lower = arb(row["B0_lower"])
            ratio_lower = arb(row["Qratio_lower"])
            if not b0_lower > 0 or not ratio_lower > 0:
                print(
                    "CERTIFICATE FAIL", delta_index, lambda_index,
                    flush=True,
                )
                return 1
            if worst is None or ratio_lower < worst[0]:
                worst = (ratio_lower, delta_index, lambda_index)
            rows += 1
    print(
        "CERTIFIED HIGH-BETA G5 RATIO SIDE4 LAMBDA3 UNIT",
        args.unit,
        rows,
        "rows",
        "worst_delta_index",
        worst[1],
        "worst_lambda_index",
        worst[2],
        "worst_Qratio_lower",
        worst[0].str(80),
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
