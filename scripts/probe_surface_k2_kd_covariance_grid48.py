"""Preregistered grid-48 conditioning judge for KD covariance."""

from __future__ import annotations

from flint import arb, ctx

import probe_surface_k2_kd_covariance as probe


GRID = 48
RADIUS_TARGET = arb(1)


def main() -> int:
    ctx.prec = probe.ARB_BITS
    mass, mean_a, mean_g, between, within, y = probe.run(GRID)
    c = (probe.T / 4).cos()
    target = (4 * c**2 - 1) / (8 * c**3)
    radius = arb(y.rad())
    passed = (
        y.is_finite()
        and arb(mass.lower()) > 0
        and y.overlaps(target)
        and arb(radius.upper()) < RADIUS_TARGET
    )
    print("KD COVARIANCE GRID", GRID)
    print("MASS", mass)
    print("MEAN_A", mean_a)
    print("MEAN_G", mean_g)
    print("BETWEEN", between)
    print("WITHIN_RADIUS", within)
    print("Y", y)
    print("Y_RADIUS", radius)
    print("TARGET", target)
    print("TARGET_OVERLAP", y.is_finite() and y.overlaps(target))
    print("RADIUS_TARGET", RADIUS_TARGET)
    print(
        "KD COVARIANCE GRID48 DESIGN "
        + ("PASS" if passed else "FAIL")
        + "; NO K2 PROMOTION"
    )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
