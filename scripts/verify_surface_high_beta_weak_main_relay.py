"""Exact rational audit of the relaxed high-beta main-saddle relay."""

from __future__ import annotations

from fractions import Fraction
import hashlib
from pathlib import Path
import platform
import subprocess


Q_LOWER = Fraction(19, 20)
RHO_UPPER = Fraction(7, 200)
MIRROR_ADVERSE_UPPER = Fraction(43, 50)
MAIN_NEGATIVE_BUDGET = Fraction(1, 20)
REST_UPPER = Fraction(1, 100_000)
MASS_RATIO_EXCESS = Fraction(1, 10**15)
ROOT = Path(__file__).resolve().parents[1]
PREREG = (
    ROOT/"docs"/
    "SURFACE-HIGH-BETA-WEAK-MAIN-RELAY-PREREG-20260728.md"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def current_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()


def verify() -> dict[str, Fraction]:
    # From |e|<=2L, L<10^-18, and d>=1/2:
    # |e|/d < 4*10^-18 < 10^-15.
    assert 4*Fraction(1, 10**18) < MASS_RATIO_EXCESS

    # d1/d=1-e/d is positive on the certified mass lane and is bounded
    # above by 1+|e|/d.  Also a/d=(d1/d)/(1-rho).
    d1_over_d_upper = 1 + MASS_RATIO_EXCESS
    one_minus_rho_lower = 1 - RHO_UPPER
    assert one_minus_rho_lower > 0
    a_over_d_upper = d1_over_d_upper/one_minus_rho_lower

    main_charge = a_over_d_upper*MAIN_NEGATIVE_BUDGET
    mirror_charge = d1_over_d_upper*MIRROR_ADVERSE_UPPER
    lower_margin = (
        Q_LOWER
        - main_charge
        - mirror_charge
        - REST_UPPER
    )
    assert lower_margin > 0
    return {
        "d1_over_d_upper": d1_over_d_upper,
        "a_over_d_upper": a_over_d_upper,
        "main_charge": main_charge,
        "mirror_charge": mirror_charge,
        "rest_charge": REST_UPPER,
        "lower_margin": lower_margin,
    }


def main() -> int:
    result = verify()
    print("HIGH-BETA WEAK-MAIN RELAY EXACT PASS")
    print("git_head", current_head())
    print("python", platform.python_version())
    print("script_sha256", sha256(Path(__file__).resolve()))
    print("prereg_sha256", sha256(PREREG))
    print("assumption Q > 19/20")
    print("assumption rho < 7/200")
    print("assumption abs(C_mirror) < 43/50")
    print("assumption X_main >= -1/20")
    print("assumption abs(C_rest) < 1/100000")
    for name, value in result.items():
        print(name, f"{value.numerator}/{value.denominator}",
              float(value))
    print(
        "SCOPE relay algebra only; weak-main interval certificate and "
        "terminal union remain open"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
