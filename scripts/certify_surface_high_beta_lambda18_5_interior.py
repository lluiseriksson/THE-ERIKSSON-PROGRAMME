"""Certify the absolute-moment interior splice for lambda>=18/5."""

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
LAMBDA0 = Fraction(18, 5)
X_SPLIT = LAMBDA0 / base.BETA0
DEPENDENCIES = (
    "scripts/certify_surface_high_beta_lambda18_5_interior.py",
    "scripts/certify_surface_high_beta_lambda4_interior.py",
    "docs/SURFACE-HIGH-BETA-LAMBDA18_5-INTERIOR-PREREG-20260728.md",
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


def rho_bound() -> tuple[arb, str]:
    worst = arb(0)
    label = ""

    def judge(lo: Fraction, hi: Fraction, moving: bool, index: int):
        nonlocal worst, label
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
        _, upper_p, _ = base.main_mass_bounds(p, beta_lower)
        lower_c, _, _ = base.main_mass_bounds(c, beta_lower)
        value = (
            base.upper(upper_p) / base.lower(lower_c)
            * (-base.lower(exponent_lower)).exp()
        )
        value_upper = base.upper(value)
        if value_upper > worst:
            worst = value_upper
            label = ("moving" if moving else "fixed") + f":{index}"

    for index in range(base.MOVING_BOXES):
        lo = X_SPLIT * index / base.MOVING_BOXES
        hi = X_SPLIT * (index + 1) / base.MOVING_BOXES
        judge(lo, hi, True, index)
    width = base.X_MAX - X_SPLIT
    for index in range(base.FIXED_BOXES):
        lo = X_SPLIT + width * index / base.FIXED_BOXES
        hi = X_SPLIT + width * (index + 1) / base.FIXED_BOXES
        judge(lo, hi, False, index)
    return worst, label


def certify() -> dict[str, object]:
    ctx.prec = 180
    p_max = Fraction(177, 250)
    c_min = Fraction(707, 1000)
    c_max = Fraction(108, 125)
    rp, hp, wp, xp = base.q_range_maxima(
        base.P0, p_max, True
    )
    rc, hc, wc, xc = base.q_range_maxima(
        c_min, c_max, False
    )
    rho, rho_label = rho_bound()
    if not rho < base.aq(Fraction(3, 200)):
        raise AssertionError(f"rho target failed: {rho}")
    adverse = (
        rho / (1 - rho) ** 2 * 4 * (rp + rc) * (hp + hc)
        + rho / (1 - rho) * xp
    )
    adverse_upper = base.upper(adverse)
    if not adverse_upper < base.aq(Fraction(9, 10)):
        raise AssertionError(f"adverse target failed: {adverse}")
    relay_margin = (
        base.aq(Fraction(19, 20))
        - base.aq(Fraction(9, 10))
        - base.aq(Fraction(1, 100_000))
    )
    assert base.lower(relay_margin) > 0
    return {
        "rho": rho,
        "rho_label": rho_label,
        "adverse": adverse_upper,
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
    print("HIGH-BETA LAMBDA18_5 INTERIOR ABSOLUTE-MOMENT PASS")
    print(
        "CONFIG beta>=1000/9 lambda>=18/5 p>=101/200 "
        f"q_boxes={base.Q_BOXES}+{base.Q_BOXES} "
        f"x_boxes={base.MOVING_BOXES}+{base.FIXED_BOXES} arb_bits=180"
    )
    print("rho", result["rho"].str(50), "worst", result["rho_label"])
    print("adverse_upper", result["adverse"].str(50), "< 9/10")
    print(
        "relay_margin",
        result["relay_margin"].str(50),
        "=19/20-9/10-1/100000>0",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
