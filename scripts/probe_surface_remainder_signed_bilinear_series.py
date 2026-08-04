"""Design probe retaining the K2 bilinear cancellation cell by cell.

The production endpoint lane currently sums KD, KF, HDD and HDF separately
and forms ``KD*HDF-KF*HDD`` afterwards.  This probe forms that bilinear on
each spatial cell before summation.  It is nominal series data only: Bessel
companion tails, outer-domain tails, and the terminal budget are not charged.
"""

from __future__ import annotations

import argparse
import json

from flint import arb, arb_series, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_series_design import (
    integrate_coefficients,
    nominal_moment_series,
)


def signed_bilinear(t: arb, base: arb, grid: int = 24, side: int = 12,
                    prec: int = 6):
    width = arb(side) / grid
    bilinear = [arb(0) for _ in range(prec)]
    kd_total = [arb(0) for _ in range(prec)]
    for i in range(grid):
        for j in range(grid):
            sigma = hull(width*i, width*(i+1))
            tau = hull(width*j, width*(j+1))
            values = nominal_moment_series(base, t, sigma, tau, prec)
            local = values["kd"]*values["hdf"] - values["kf"]*values["hdd"]
            area = 4*width**2
            for order, value in enumerate(local.coeffs()):
                bilinear[order] += area*value
            for order, value in enumerate(values["kd"].coeffs()):
                kd_total[order] += area*value
    b_series = arb_series(bilinear, prec)
    kd_series = arb_series(kd_total, prec)
    # B(0)=0 is an exact analytic identity; retain its computed interval as a
    # diagnostic rather than silently replacing it before it is audited.
    return b_series, kd_series, None


def safe_square_series(series: arb_series, prec: int) -> list[arb]:
    """Square a series but enclose the positive constant by endpoints."""
    coeffs = series.coeffs()
    constant = hull(coeffs[0].lower()**2, coeffs[0].upper()**2)
    result = [arb(0) for _ in range(prec)]
    result[0] = constant
    for n in range(1, prec):
        result[n] = sum((coeffs[j]*coeffs[n-j]
                         for j in range(n+1)), arb(0))
    return result


def quotient_y3(b_series: arb_series, kd_series: arb_series, t: arb,
                prec: int = 6) -> arb:
    """Formal quotient coefficient y_3, with a dependency-safe denominator."""
    # Full moments include H0/K0 already, hence Y=4*B/(delta*KD^2).
    d = [value/4 for value in safe_square_series(kd_series, prec)]
    q = [b_series.coeffs()[k+1] for k in range(prec-1)]
    y = [arb(0) for _ in range(prec-1)]
    for n in range(prec-1):
        correction = sum((d[j]*y[n-j] for j in range(1, n+1)), arb(0))
        y[n] = (q[n]-correction)/d[0]
    return y[3]


def run() -> dict:
    ctx.prec = 140
    t = arb("2.9")
    base = hull(arb(0), arb("0.001"))
    out = {}
    for grid in (12, 24, 48, 96):
        signed_b, kd, _ = signed_bilinear(t, base, grid=grid)
        separate = integrate_coefficients(t, grid=grid, base=base)
        separate_series = {name: arb_series(value, 6)
                           for name, value in separate.items()}
        separate_b = (separate_series["kd"]*separate_series["hdf"]
                      - separate_series["kf"]*separate_series["hdd"])
        out[str(grid)] = {
            "signed_B0": signed_b.coeffs()[0].str(12),
            "signed_B4_radius": signed_b.coeffs()[4].rad().str(12),
            "separate_B4_radius": separate_b.coeffs()[4].rad().str(12),
            "signed_Y3_radius": quotient_y3(signed_b, kd, t).rad().str(12),
            "separate_Y3_radius": quotient_y3(separate_b,
                                                separate_series["kd"],
                                                t).rad().str(12),
            "signed_KD0_lower": kd.coeffs()[0].lower().str(12),
        }
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="scripts/probe_surface_remainder_signed_bilinear_series.json")
    args = parser.parse_args()
    payload = {"results": run(), "scope": "design-only; no K2 promotion"}
    text = json.dumps(payload, indent=2)
    print(text)
    with open(args.output, "w", encoding="utf-8") as handle:
        handle.write(text + "\n")


if __name__ == "__main__":
    main()
