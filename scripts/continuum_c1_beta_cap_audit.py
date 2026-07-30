#!/usr/bin/env python3
"""Deterministic numerical audit of the CONTINUUM-C1 KP beta cap.

This is a binary64 diagnostic, not a proof. The proof is the Lean theorem
`YangMills.ContinuumC1.beta_lt_kpBetaCap`.
"""

from __future__ import annotations

import json
import math
import platform


def beta_cap(dimension: int, colors: int) -> float:
    if dimension < 1:
        raise ValueError("dimension must be positive")
    if colors < 1:
        raise ValueError("colors must be positive")
    radius_constant = (16 * dimension + 1) ** 2
    return math.log1p(math.exp(-3) / radius_constant) / colors


def main() -> None:
    cases = [(4, 3), (4, 2), (3, 2)]
    rows = [
        {
            "dimension": d,
            "colors": nc,
            "radius_square": (16 * d + 1) ** 2,
            "beta_cap": f"{beta_cap(d, nc):.12e}",
        }
        for d, nc in cases
    ]
    print(
        json.dumps(
            {
                "classification": "VERIFIED binary64 diagnostic; not a proof",
                "formula": "log1p(exp(-3)/(16*d+1)^2)/Nc",
                "python": platform.python_version(),
                "rows": rows,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
