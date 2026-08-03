#!/usr/bin/env python3
"""Deterministic arithmetic audit for the CONTINUUM-C1 Haar tail.

This script is not a proof and never upgrades a result to PROVED.  It checks
the exact rational algebra and the threshold quantifiers used by the analytic
and Lean arguments.
"""

from __future__ import annotations

import argparse
import json
import platform
from fractions import Fraction


def audit(nc: int, a_num: int, a_den: int, radius: int) -> dict[str, object]:
    if nc < 2:
        raise ValueError("nc must be at least 2")
    if a_num <= 0 or a_den <= 0:
        raise ValueError("the lattice spacing must be positive")
    if radius < 0:
        raise ValueError("radius must be nonnegative")

    a = Fraction(a_num, a_den)
    tail_mass = Fraction(1, 3)
    threshold = Fraction(nc, 2) / (a**4)

    # The affine rearrangement behind the probability lower bound.
    upper_if_mass_one_third = (
        Fraction(nc, 2) + Fraction(3 * nc, 2) * tail_mass
    )
    assert upper_if_mass_one_third == nc

    return {
        "classification": "VERIFIED arithmetic diagnostic; not a proof",
        "python": platform.python_version(),
        "inputs": {
            "nc": nc,
            "a": f"{a.numerator}/{a.denominator}",
            "compact_radius": radius,
        },
        "tail_mass_lower_bound": "1/3",
        "tail_threshold": f"{threshold.numerator}/{threshold.denominator}",
        "threshold_strictly_outside_compact": threshold > radius,
        "identity_check": (
            "Nc/2 + (3*Nc/2)*(1/3) = Nc"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--nc", type=int, default=2)
    parser.add_argument("--a-num", type=int, default=1)
    parser.add_argument("--a-den", type=int, default=10)
    parser.add_argument("--radius", type=int, default=1000)
    args = parser.parse_args()
    print(
        json.dumps(
            audit(args.nc, args.a_num, args.a_den, args.radius),
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
