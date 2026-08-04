"""Certify the x-correlated high-beta interior splice for lambda>=3."""

from __future__ import annotations

from fractions import Fraction
import hashlib
from pathlib import Path
import platform
import subprocess

import flint
from flint import arb, ctx

import certify_surface_high_beta_lambda4_interior as base


ROOT = Path(__file__).resolve().parents[1]
LAMBDA0 = Fraction(3, 1)
X_SPLIT = LAMBDA0 / base.BETA0
MOVING_BOXES = 512
FIXED_BOXES = 2048
DEPENDENCIES = (
    "scripts/certify_surface_high_beta_lambda3_joint_interior.py",
    "scripts/certify_surface_high_beta_lambda4_interior.py",
    "docs/SURFACE-HIGH-BETA-LAMBDA3-JOINT-INTERIOR-PREREG-20260728.md",
    "docs/SURFACE-HIGH-BETA-LAMBDA4-INTERIOR-PREREG-20260728.md",
)


def sha256(relative: str) -> str:
    return hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()


def current_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()


def judge_box(
    lo: Fraction,
    hi: Fraction,
    moving: bool,
) -> tuple[arb, arb]:
    x = base.hull(base.aq(lo), base.aq(hi))
    p = ((arb.pi() - x) / 4).sin()
    c = ((arb.pi() - x) / 4).cos()
    if moving:
        beta_lower = base.aq(LAMBDA0 / hi)
        exponent_lower = (
            base.aq(LAMBDA0)
            * arb(2).sqrt()
            * (1 - base.aq(hi) ** 2 / 96)
        )
    else:
        beta_lower = base.aq(base.BETA0)
        exponent_lower = (
            4
            * beta_lower
            * arb(2).sqrt()
            * (base.aq(lo) / 4).sin()
        )

    p_floor = base.lower(p)
    c_floor = base.lower(c)
    rp, hp, _, xp = base.moment_coefficients(
        p, beta_lower, base.radius_floor(p_floor, True)
    )
    rc, hc, _, _ = base.moment_coefficients(
        c, beta_lower, base.radius_floor(c_floor, False)
    )
    _, upper_p, _ = base.main_mass_bounds(p, beta_lower)
    lower_c, _, _ = base.main_mass_bounds(c, beta_lower)
    rho = base.upper(
        base.upper(upper_p)
        / base.lower(lower_c)
        * (-base.lower(exponent_lower)).exp()
    )
    if not rho < base.aq(Fraction(1, 25)):
        raise AssertionError(f"rho target failed on x=[{lo},{hi}]: {rho}")
    adverse = base.upper(
        rho / (1 - rho) ** 2 * 4 * (rp + rc) * (hp + hc)
        + rho / (1 - rho) * xp
    )
    return rho, adverse


def certify() -> dict[str, object]:
    ctx.prec = 180
    worst_rho = arb(0)
    worst_adverse = arb(0)
    rho_label = ""
    adverse_label = ""

    def sweep(
        left: Fraction,
        right: Fraction,
        boxes: int,
        moving: bool,
    ) -> None:
        nonlocal worst_rho, worst_adverse, rho_label, adverse_label
        width = right - left
        lane = "moving" if moving else "fixed"
        for index in range(boxes):
            lo = left + width * index / boxes
            hi = left + width * (index + 1) / boxes
            rho, adverse = judge_box(lo, hi, moving)
            if rho > worst_rho:
                worst_rho = rho
                rho_label = f"{lane}:{index}"
            if adverse > worst_adverse:
                worst_adverse = adverse
                adverse_label = f"{lane}:{index}"

    sweep(Fraction(0), X_SPLIT, MOVING_BOXES, True)
    sweep(X_SPLIT, base.X_MAX, FIXED_BOXES, False)
    if not worst_adverse < base.aq(Fraction(9, 10)):
        raise AssertionError(f"joint adverse target failed: {worst_adverse}")
    relay_margin = (
        base.aq(Fraction(19, 20))
        - base.aq(Fraction(9, 10))
        - base.aq(Fraction(1, 100_000))
    )
    assert base.lower(relay_margin) > 0
    return {
        "rho": worst_rho,
        "rho_label": rho_label,
        "adverse": worst_adverse,
        "adverse_label": adverse_label,
        "relay_margin": relay_margin,
    }


def main() -> int:
    print("PROVENANCE git_head", current_head())
    print("PROVENANCE python", platform.python_version())
    print("PROVENANCE python_flint", flint.__version__)
    print("PROVENANCE arb_bits", 180)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(relative))
    result = certify()
    print("HIGH-BETA LAMBDA3 JOINT INTERIOR PASS")
    print(
        "CONFIG beta>=1000/9 lambda>=3 p>=101/200 "
        f"x_boxes={MOVING_BOXES}+{FIXED_BOXES} arb_bits=180"
    )
    print(
        "rho",
        result["rho"].str(50),
        "worst",
        result["rho_label"],
        "< 1/25",
    )
    print(
        "joint_adverse_upper",
        result["adverse"].str(50),
        "worst",
        result["adverse_label"],
        "< 9/10",
    )
    print(
        "relay_margin",
        result["relay_margin"].str(50),
        "=19/20-9/10-1/100000>0",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
