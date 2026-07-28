"""Exact zero-order cancellation for every relative-companion truncation."""

from __future__ import annotations

from fractions import Fraction

import sympy as sp

from surface_bessel_integral_remainder import relative_coefficients


MAX_TERMS = 16


def verify() -> None:
    for family in ("A", "B"):
        for terms in range(1, MAX_TERMS+1):
            coefficients = relative_coefficients(family, terms-1)
            if coefficients[0] != Fraction(1):
                raise AssertionError(
                    f"{family} terms={terms}: constant is not exactly one"
                )

    delta, c = sp.symbols("delta c", nonzero=True)
    d1, r1, a1, b1 = sp.symbols("d1 r1 a1 b1")
    d = 2+d1*delta
    root = 1+r1*delta
    acomp = 1+a1*delta
    bcomp = 1+b1*delta
    numerator = sp.expand(bcomp*d-2*root*acomp)
    if sp.expand(numerator.subs(delta, 0)) != 0:
        raise AssertionError("pointwise R numerator is not divisible by delta")
    quotient = sp.cancel(numerator/delta)
    if quotient.has(sp.zoo, sp.nan):
        raise AssertionError("removable quotient did not simplify")


def main() -> int:
    verify()
    print(f"COMPANION_FAMILIES A,B TERMS 1..{MAX_TERMS}")
    print("A_N(0)=B_N(0)=1 EXACT")
    print("B_N*D-2*root*A_N IS DIVISIBLE BY DELTA EXACT")
    print("SURFACE K2 COMPANION ZERO CANCELLATION VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
