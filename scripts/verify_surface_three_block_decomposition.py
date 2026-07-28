"""Exact three-block decomposition of the high-beta bilinear scalar.

The torus is split into the main square, its mirror square, and the rest.
This script verifies the second assembly step algebraically.  It makes no
analytic sign or size claim.
"""

from __future__ import annotations

import sympy as sp


def identities() -> dict[str, sp.Expr]:
    d1, f1, u1, w1 = sp.symbols("d_1 f_1 u_1 w_1", nonzero=True)
    e, k, y, z = sp.symbols("e k y z")
    beta = sp.symbols("beta", positive=True)
    kappa = 4 * beta**3

    d = d1 + e
    f = f1 + k
    u = u1 + y
    w = w1 + z
    r1 = f1 / d1

    x1 = sp.cancel(kappa * (d1 * w1 - f1 * u1) / d1**2)
    xfull = sp.cancel(kappa * (d * w - f * u) / d**2)

    assembled = sp.cancel(
        d1 / d * x1
        + kappa / d * (z - r1 * y)
        + kappa * (u1 + y) / d**2 * (e * r1 - k)
    )
    assert sp.cancel(xfull - assembled) == 0

    adverse = sp.cancel(xfull - d1 / d * x1)
    adverse_expanded = sp.cancel(
        kappa / d**2
        * (
            d1 * z
            + e * z
            - f1 * y
            + e * f1 * u1 / d1
            - k * u1
            - k * y
        )
    )
    assert sp.cancel(adverse - adverse_expanded) == 0

    return {
        "x1": x1,
        "xfull": xfull,
        "assembled": assembled,
        "rest_adverse": adverse,
        "rest_adverse_expanded": adverse_expanded,
    }


def main() -> int:
    result = identities()
    print("THREE-BLOCK BILINEAR DECOMPOSITION ALGEBRA PASS")
    for name, value in result.items():
        print(name, "=", value)
    print(
        "CONTRACT: first combine B and B' into (d1,f1,u1,w1,X1); "
        "then add the rest (e,k,y,z) with the displayed exact identity."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
