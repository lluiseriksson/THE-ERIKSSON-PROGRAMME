"""Exact audit of the two-group high-beta bilinear residual.

The grouping removes the artificial growth caused by bounding the six
full-minus-main products separately.  No numerical or K4 claim is made here.
"""

import sympy as sp


def verify():
    a, b, f, g, u, v, w, x, beta = sp.symbols(
        "a b f g u v w x beta", nonzero=True
    )
    k = 4 * beta**3
    full_d = a + b
    full = sp.cancel(
        k * (full_d * (w + x) - (f + g) * (u + v)) / full_d**2
    )
    main = sp.cancel(k * (a * w - f * u) / a**2)
    ratio = f / a

    six_term_residual = a * x + b * w + b * x - f * v - g * u - g * v
    identity_a = sp.cancel(
        (a / full_d) ** 2 * main
        + k * six_term_residual / full_d**2
    )
    assert sp.cancel(full - identity_a) == 0

    # Division-free in the mirror mass b: only the main ratio f/a remains.
    grouped = sp.cancel(
        a / full_d * main
        + k / full_d * (x - ratio * v)
        + k * (u + v) / full_d**2 * (b * ratio - g)
    )
    assert sp.cancel(full - grouped) == 0

    difference = sp.cancel(
        k * six_term_residual / full_d**2
        - main * b * (2 * a + b) / full_d**2
    )
    assert sp.cancel(full - main - difference) == 0

    adverse = sp.cancel(
        k / full_d * (ratio * v - x)
        + k * (u + v) / full_d**2 * (g - b * ratio)
    )
    assert sp.cancel(grouped - (a / full_d * main - adverse)) == 0
    return {
        "full": full,
        "main": main,
        "grouped": grouped,
        "adverse": adverse,
    }


def main() -> int:
    verify()
    print("HIGH-BETA BILINEAR RESIDUAL ALGEBRA PASS")
    print(
        "X_full=(a/(a+b))*X_main"
        "+4 beta^3/(a+b)*(x-(f/a)v)"
        "+4 beta^3*(u+v)/(a+b)^2*(b(f/a)-g)"
    )
    print(
        "SUFFICIENT CONTRACT: adverse_grouped < 19/20, "
        "given a>0, a+b>0, X_main>=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
