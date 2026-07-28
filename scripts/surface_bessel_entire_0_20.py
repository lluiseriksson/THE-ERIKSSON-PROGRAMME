"""Experimental positive-series Bessel enclosure on ``0 <= z <= 20``.

This is deliberately separate from the production companion modules.  It
uses the positive entire series for ``I_1(z)/z`` and ``I_2(z)/z**2`` with an
explicit geometric tail and complete-monotonicity endpoint hulls.  No gate
or manifest may import it until an independent audit accepts the bound.
"""

from math import comb, factorial

from flint import arb


Z_MAX = 20
TERMS = 160


def _falling(n: int, order: int) -> int:
    out = 1
    for j in range(order):
        out *= n - j
    return out if n >= order else 0


def _coeff(family: str, k: int) -> arb:
    if family == "A":
        return arb(1) / (2 * arb(4) ** k * factorial(k) * factorial(k + 1))
    if family == "B":
        return arb(1) / (arb(4) ** (k + 1) * factorial(k) * factorial(k + 2))
    raise ValueError(family)


def _base_derivatives(x: arb, family: str, order: int) -> list[arb]:
    xmax = arb(x.abs_upper())
    if x.lower() < 0 or xmax > Z_MAX:
        raise ValueError("entire 0..20 enclosure requires 0<=z<=20")
    out = [arb(0) for _ in range(order + 1)]
    for k in range(TERMS):
        coefficient = _coeff(family, k)
        degree = 2 * k
        for derivative in range(order + 1):
            if degree >= derivative:
                out[derivative] += (
                    coefficient * _falling(degree, derivative)
                    * x ** (degree - derivative)
                )

    # At z=20 and k=160 the next/previous ratio is < 1e-2.  The
    # derivative-majorant uses xmax so it remains valid on an interval.
    for derivative in range(order + 1):
        k = TERMS
        degree = 2 * k
        coefficient = _coeff(family, k)
        next_coefficient = _coeff(family, k + 1)
        first = (
            coefficient * _falling(degree, derivative)
            * xmax ** (degree - derivative)
            if degree >= derivative else arb(0)
        )
        second = next_coefficient * _falling(degree + 2, derivative) * xmax ** (
            degree + 2 - derivative
        )
        ratio = second / first if first != 0 else arb(0)
        if not ratio < 1:
            raise ValueError("entire-series tail is not contractive")
        out[derivative] += first / (1 - ratio) * arb("0 +/- 1")
    return out


def _point_derivatives(x: arb, family: str, order: int) -> list[arb]:
    base = _base_derivatives(x, family, order)
    return [
        (-x).exp()
        * sum(
            (arb(comb(n, k)) * (-1) ** (n - k) * base[k]
             for k in range(n + 1)),
            arb(0),
        )
        for n in range(order + 1)
    ]


def entire_outer_derivatives(
    z: arb, family: str, order: int = 4
) -> list[arb]:
    """Return interval enclosures for derivatives through ``order``."""
    if z.lower() < 0 or z.upper() > Z_MAX:
        raise ValueError("entire 0..20 enclosure requires 0<=z<=20")
    zl, zh = arb(z.lower()), arb(z.upper())
    lo = _point_derivatives(zl, family, order)
    hi = _point_derivatives(zh, family, order)
    # Complete monotonicity fixes the endpoint ordering of each derivative.
    return [
        ((lo[n] + hi[n]) / 2 + (hi[n] - lo[n]) / 2 * arb("0 +/- 1"))
        for n in range(order + 1)
    ]


if __name__ == "__main__":
    from flint import ctx

    ctx.prec = 140
    for z_text in ("0.1", "4", "8", "12", "16", "20"):
        z = arb(z_text)
        for family, nu in (("A", 1), ("B", 2)):
            values = entire_outer_derivatives(z, family)
            exact = (-z).exp() * z.bessel_i(nu) / (z if family == "A" else z**2)
            assert values[0].contains(exact), (z, family, values[0], exact)
    print("ENTIRE 0..20 POINT REGRESSION PASS")
