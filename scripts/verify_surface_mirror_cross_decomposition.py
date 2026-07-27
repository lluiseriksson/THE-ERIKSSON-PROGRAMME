"""Exact audit of the mirror-transformed high-beta adverse scalar.

This script is algebra only.  It records the cancellation that must be
preserved by any analytic or interval bound after applying the mirror
involution.  It makes no numerical sign claim.
"""

from __future__ import annotations

import sympy as sp


def identities() -> dict[str, sp.Expr]:
    a, f, u, w = sp.symbols("a f u w", nonzero=True)
    ap, fp, up, wp = sp.symbols("a_p f_p u_p w_p")
    scale, beta = sp.symbols("S beta", positive=True)
    kappa = 4 * beta**3

    b = -scale * ap
    g = -scale * fp
    v = scale * up
    x = scale * wp
    d = a + b
    r = f / a

    adverse = sp.cancel(
        kappa / d * (r * v - x)
        + kappa * (u + v) / d**2 * (g - b * r)
    )
    cross = sp.cancel(
        kappa * scale / d**2
        * (f * up - a * wp + u * (ap * r - fp))
    )
    mirror_determinant = sp.cancel(
        kappa * scale**2 / d**2 * (ap * wp - fp * up)
    )
    xp = sp.cancel(kappa * (ap * wp - fp * up) / ap**2)
    weighted_xp = sp.cancel((scale * ap / d) ** 2 * xp)

    assert sp.cancel(adverse - cross - mirror_determinant) == 0
    assert sp.cancel(mirror_determinant - weighted_xp) == 0

    ratio_cross = sp.cancel(
        kappa * scale / d**2
        * (a * (r * up - wp) + u * ap * (r - fp / ap))
    )
    assert sp.cancel(cross - ratio_cross) == 0

    rho = sp.symbols("rho", positive=True)
    rp, h, hp = sp.symbols("r_p h h_p")
    ratio_reduced = (
        kappa * rho / (1 - rho) ** 2 * (r - rp) * (h + hp)
        - rho / (1 - rho) * xp
    )
    substitutions = {
        scale: rho * a / ap,
        fp: rp * ap,
        u: h * a,
        up: hp * ap,
        wp: ap * (rp * hp + xp / kappa),
    }
    assert sp.cancel(adverse.subs(substitutions) - ratio_reduced) == 0

    return {
        "adverse": adverse,
        "cross": cross,
        "mirror_determinant": mirror_determinant,
        "weighted_xp": weighted_xp,
        "ratio_cross": ratio_cross,
        "ratio_reduced": ratio_reduced,
    }


def main() -> int:
    result = identities()
    print("MIRROR CROSS DECOMPOSITION ALGEBRA PASS")
    for name, value in result.items():
        print(name, "=", value)
    print(
        "CONTRACT: with rho=S*a_p/a, r=f/a, r_p=f_p/a_p, "
        "h=u/a, h_p=u_p/a_p,\n"
        "adverse = 4*beta^3*rho/(1-rho)^2"
        "*(r-r_p)*(h+h_p) - rho/(1-rho)*X_p"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
