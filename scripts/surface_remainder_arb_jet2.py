"""Arb design prototype for K2/K3-compliant Bessel jets."""

from __future__ import annotations

from dataclasses import dataclass
from math import factorial

import mpmath as mp
from flint import arb, ctx


def hull(lo: arb, hi: arb) -> arb:
    return (lo + hi) / 2 + (hi - lo) / 2 * arb("0 +/- 1")


def symmetric(radius: arb) -> arb:
    return radius * arb("0 +/- 1")


@dataclass(frozen=True)
class Jet2:
    c0: arb
    c1: arb
    c2: arb


def compose(z: Jet2, f0: arb, f1: arb, f2: arb) -> Jet2:
    return Jet2(f0, f1 * z.c1, f1 * z.c2 + f2 * z.c1**2 / 2)


def falling(n: int, order: int) -> int:
    out = 1
    for value in range(n - order + 1, n + 1):
        out *= value
    return out if n >= order else 0


def series_derivatives(z: arb, family: str, terms: int = 8) -> tuple[arb, arb, arb]:
    """Entire enclosures on a small ball, including explicit derivative tails."""

    zmax = arb(z.abs_upper())
    sums = [arb(0), arb(0), arb(0)]
    for k in range(terms):
        if family == "g":
            coefficient = arb(1) / (arb(2) * arb(4) ** k * factorial(k) * factorial(k + 1))
        else:
            coefficient = arb(1) / (arb(4) ** (k + 1) * factorial(k) * factorial(k + 2))
        degree = 2 * k
        for order in range(3):
            multiplier = falling(degree, order)
            if multiplier:
                sums[order] += coefficient * multiplier * z ** (degree - order)

    # Bound every derivative tail by its first omitted absolute term and a
    # geometric ratio upper bound.  Ratios decrease with k; evaluate the
    # ratio of the next two omitted derivative terms explicitly.
    for order in range(3):
        k = terms
        degree = 2 * k
        if family == "g":
            coefficient = arb(1) / (arb(2) * arb(4) ** k * factorial(k) * factorial(k + 1))
            next_coefficient = arb(1) / (
                arb(2) * arb(4) ** (k + 1) * factorial(k + 1) * factorial(k + 2)
            )
        else:
            coefficient = arb(1) / (arb(4) ** (k + 1) * factorial(k) * factorial(k + 2))
            next_coefficient = arb(1) / (
                arb(4) ** (k + 2) * factorial(k + 1) * factorial(k + 3)
            )
        first = coefficient * falling(degree, order) * zmax ** (degree - order)
        second = (
            next_coefficient
            * falling(degree + 2, order)
            * zmax ** (degree + 2 - order)
        )
        ratio = second / first if bool(first > 0) else arb(0)
        assert bool(ratio < arb(1) / 2)
        sums[order] += symmetric(first / (1 - ratio))
    return sums[0], sums[1], sums[2]


def g_derivatives(z: arb) -> tuple[arb, arb, arb]:
    if z.lower() <= 0:
        assert z.upper() <= arb("0.1")
        return series_derivatives(z, "g")
    i0, i1 = z.bessel_i(0), z.bessel_i(1)
    return (
        i1 / z,
        i0 / z - 2 * i1 / z**2,
        i1 / z - 3 * i0 / z**2 + 6 * i1 / z**3,
    )


def h_derivatives(z: arb) -> tuple[arb, arb, arb]:
    if z.lower() <= 0:
        assert z.upper() <= arb("0.1")
        return series_derivatives(z, "h")
    i0, i1 = z.bessel_i(0), z.bessel_i(1)
    return (
        i0 / z**2 - 2 * i1 / z**3,
        i1 / z**2 - 4 * i0 / z**3 + 8 * i1 / z**4,
        i0 / z**2 - 7 * i1 / z**3 + 20 * i0 / z**4 - 40 * i1 / z**5,
    )


def contains_value(ball: arb, value: mp.mpf) -> bool:
    return ball.contains(arb(str(value)))


def check() -> None:
    ctx.prec = 180
    mp.mp.dps = 80
    boxes = ((0, mp.mpf("0.05")), (mp.mpf("0.2"), mp.mpf("0.3")),
             (mp.mpf("3.9"), mp.mpf("4.1")), (mp.mpf("79"), mp.mpf("81")))
    for lo, hi in boxes:
        zball = hull(arb(str(lo)), arb(str(hi)))
        for derivatives, fn in (
            (g_derivatives(zball), lambda x: mp.besseli(1, x) / x if x else mp.mpf("0.5")),
            (h_derivatives(zball), lambda x: mp.besseli(2, x) / x**2 if x else mp.mpf("0.125")),
        ):
            for sample in (lo, (lo + hi) / 2, hi):
                values = (fn(sample), mp.diff(fn, sample, 1), mp.diff(fn, sample, 2))
                assert all(contains_value(ball, value) for ball, value in zip(derivatives, values))
    print("Arb K2/K3 Bessel derivative enclosures contain all sample derivatives")


if __name__ == "__main__":
    check()
