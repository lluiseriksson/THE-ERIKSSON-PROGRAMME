"""Rouché zero-free certificate for integrated fixed-square surrogate KD."""

from __future__ import annotations

from pathlib import Path

from flint import acb, arb, ctx

import probe_surface_k2_fixed_square_complex_supremum as base
from surface_bessel_integral_remainder import relative_coefficients


ROOT = Path(__file__).resolve().parents[1]
GEOMETRY_PRODUCTION = (
    ROOT/"outputs"/
    "surface-k2-r8-fixed-square-complex-geometry-production-20260728.txt"
)
GEOMETRY_REPLAY = (
    ROOT/"outputs"/
    "surface-k2-r8-fixed-square-complex-geometry-replay-20260728.txt"
)
GEOMETRY_PASS = "K2 R8 FIXED-SQUARE COMPLEX GEOMETRY PASS"
COMPANION_ORDER = 8
LADDER = ((24, 32), (48, 64), (96, 128))


def require_geometry():
    production = GEOMETRY_PRODUCTION.read_text(encoding="utf-8")
    replay = GEOMETRY_REPLAY.read_text(encoding="utf-8")
    if GEOMETRY_PASS not in production or production != replay:
        raise RuntimeError("degree-eight geometry gate is not reproducible")


def companion_a(h):
    total = acb(0)
    for coefficient in reversed(
        relative_coefficients("A", COMPANION_ORDER)
    ):
        total = (
            total*h
            + arb(coefficient.numerator)/coefficient.denominator
        )
    return total


def kd_integrand(delta, sigma, alpha):
    c = (base.T/4).cos()
    p = base.p_over_delta(delta, sigma)
    q = base.p_over_delta(delta, alpha)
    w = p+q-delta*p*q/c**2
    root = (1-delta*w).sqrt()
    phase = -4*c*w/(1+root)
    h = delta/(4*c*root)
    d_weight = 2*(1-delta*(p+q))
    common = 1/(2*arb.pi()).sqrt()
    kernel = (
        2*common/(4*c)**(arb(3)/2)
        / root/root.sqrt()
        * companion_a(h)*phase.exp()
    )
    return kernel*d_weight


def integrate_zero(grid):
    width = base.SIDE/grid
    total = acb(0)
    for i in range(grid):
        for j in range(grid):
            sigma = base.hull(width*i, width*(i+1))
            alpha = base.hull(width*j, width*(j+1))
            total += (
                4*width**2
                * kd_integrand(acb(0), sigma, alpha)
            )
    return total


def boundary_difference(grid, theta_index, theta_count):
    delta = base.theta_arc(theta_index, theta_count)
    width = base.SIDE/grid
    total = acb(0)
    for i in range(grid):
        for j in range(grid):
            sigma = base.hull(width*i, width*(i+1))
            alpha = base.hull(width*j, width*(j+1))
            total += 4*width**2*(
                kd_integrand(delta, sigma, alpha)
                - kd_integrand(acb(0), sigma, alpha)
            )
    return delta, total


def run_level(grid, theta_count):
    kd0 = integrate_zero(grid)
    kd0_lower = arb(abs(kd0).lower())
    worst = arb(0)
    for index in range(theta_count):
        delta, difference = boundary_difference(
            grid, index, theta_count
        )
        upper = arb(abs(difference).upper())
        worst = max(worst, upper)
        print(
            "ARC",
            index,
            "DELTA",
            delta,
            "DIFF_ABS_UPPER",
            upper,
            flush=True,
        )
    return kd0_lower, worst


def main():
    ctx.prec = 140
    require_geometry()
    print("K2 R8 INTEGRATED-KD ROUCHE CERTIFICATE")
    print("rho", base.RHO, "companion_order", COMPANION_ORDER)
    passed = False
    for grid, theta_count in LADDER:
        kd0_lower, worst = run_level(grid, theta_count)
        passed = kd0_lower > 0 and worst < kd0_lower
        print(
            "LEVEL",
            grid,
            theta_count,
            "KD0_ABS_LOWER",
            kd0_lower,
            "BOUNDARY_DIFF_ABS_UPPER",
            worst,
            "PASS",
            passed,
            flush=True,
        )
        if passed:
            break
    print(
        "K2 R8 INTEGRATED-KD ROUCHE "
        + ("PASS" if passed else "FAIL")
        + "; TRUE COMPANION, EXTERIOR, AND K2 OPEN",
        flush=True,
    )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
