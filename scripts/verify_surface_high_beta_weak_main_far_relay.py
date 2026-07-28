"""Exact rational far-zone relay from X_main >= -1/20."""

from __future__ import annotations

from fractions import Fraction
import hashlib
from pathlib import Path
import platform
import subprocess


ROOT = Path(__file__).resolve().parents[1]
Q_LOWER = Fraction(19, 20)
MAIN_NEGATIVE_BUDGET = Fraction(1, 20)
MIRROR_DIFFERENCE = Fraction(1, 10**30)
REST_DIFFERENCE = Fraction(1, 100_000)
DEPENDENCIES = (
    "scripts/verify_surface_high_beta_weak_main_far_relay.py",
    "docs/SURFACE-K2-WEAK-MAIN-COVARIANCE-FAR-PREREG-20260728.md",
    "docs/SURFACE-HIGH-BETA-FAR-MIRROR-BOUND-20260727.md",
    "scripts/verify_surface_high_beta_far_mirror_bound.py",
    "scripts/verify_surface_high_beta_rest_perturbation_bound.py",
)


def sha256(relative: str) -> str:
    return hashlib.sha256((ROOT/relative).read_bytes()).hexdigest().upper()


def current_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()


def verify() -> dict[str, Fraction]:
    margin = (
        Q_LOWER
        - MAIN_NEGATIVE_BUDGET
        - MIRROR_DIFFERENCE
        - REST_DIFFERENCE
    )
    assert margin > Fraction(899, 1000)
    return {
        "q_lower": Q_LOWER,
        "main_charge": MAIN_NEGATIVE_BUDGET,
        "mirror_charge": MIRROR_DIFFERENCE,
        "rest_charge": REST_DIFFERENCE,
        "lower_margin": margin,
    }


def main() -> int:
    result = verify()
    print("HIGH-BETA WEAK-MAIN FAR RELAY EXACT PASS")
    print("git_head", current_head())
    print("python", platform.python_version())
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(relative))
    for name, value in result.items():
        print(name, f"{value.numerator}/{value.denominator}")
    print("lower_margin_decimal", float(result["lower_margin"]))
    print(
        "SCOPE far-zone relay algebra only; "
        "far weak-main interval certificate remains required"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
