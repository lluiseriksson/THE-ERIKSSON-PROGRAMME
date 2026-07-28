"""Nominal K2 ratio-factorization conditioning probe.

The implementation keeps the production product-of-sums object, but extracts
the exact delta-zero defect g=r-(r0/2)d before interval products.  It is a
truncated-series design experiment, not a certificate.
"""

from __future__ import annotations

import argparse
import json

from flint import arb, arb_series, ctx

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_series_design import (
    PREC, aq, relative_polynomial_series, sinc2_affine_delta,
)


NAMES = ("gd", "df", "gf", "dd")


def eval_series(value: arb_series, x: arb) -> arb:
    out = arb(0)
    for coeff in reversed(value.coeffs()):
        out = out * x + coeff
    return out


def ratio_series(t, sigma, tau):
    delta = arb_series([arb(0), arb(1)], PREC)
    p = sigma**2 / 4 * sinc2_affine_delta(arb(0), sigma**2 / 4, PREC)
    q = tau**2 / 4 * sinc2_affine_delta(arb(0), tau**2 / 4, PREC)
    c = (t / 4).cos()
    c2, cc = c**2, 2 * c**2 - 1
    w = p + q - delta * p * q / c2
    root = (1 - delta * w).sqrt()
    phase = -4 * c * w / (1 + root)
    h = delta / (4 * c * root)
    dw = 2 * (1 - delta * (p + q))
    bracket = (-2 * cc * delta * p - cc * delta * q + 2 * cc + 1
               + 2 * delta**2 * p * q - delta * p - 2 * delta * q)
    fo = -4 * p * bracket
    common = 1 / (2 * arb.pi()).sqrt()
    exponential = phase.exp()
    hh = (common / (4 * c)**(arb(5) / 2)
          * root**(-arb(5) / 2)
          * relative_polynomial_series(h, "B") * exponential)
    # The ratio K/H cancels the common exponential exactly.
    ratio = (8 * c * root * relative_polynomial_series(h, "A")
             / relative_polynomial_series(h, "B"))
    r0 = (8 * c * aq(relative_coefficients("A", 4)[0])
          / aq(relative_coefficients("B", 4)[0]))
    g = ratio - r0 * dw / 2
    return hh, dw, fo, g, r0


def integrate(t_text: str, grid: int = 12, return_series: bool = False):
    t = arb(t_text)
    width = arb(12) / grid
    totals = {name: [arb(0) for _ in range(PREC)] for name in NAMES}
    g0_bad = 0
    g0_rows = []
    for i in range(grid):
        for j in range(grid):
            sigma = hull(width * i, width * (i + 1))
            tau = hull(width * j, width * (j + 1))
            hh, d, fo, g, r0 = ratio_series(t, sigma, tau)
            g0 = g.coeffs()[0]
            if not g0.contains(arb(0)):
                g0_bad += 1
            g0_rows.append(g0)
            coeffs = g.coeffs()
            coeffs[0] = arb(0)
            go = arb_series(coeffs[1:] + [arb(0)], PREC)
            values = {
                "gd": hh * d * go,
                "df": hh * d * fo,
                "gf": hh * fo * go,
                "dd": hh * d * d,
            }
            area = 4 * width**2
            for name, value in values.items():
                for k, coeff in enumerate(value.coeffs()):
                    totals[name][k] += area * coeff
    series = {name: arb_series(values, PREC) for name, values in totals.items()}
    bover = series["gd"] * series["df"] - series["gf"] * series["dd"]
    lane = hull(arb(0), arb("0.0125"))
    value = eval_series(bover, lane)
    result = {
        "t": t_text,
        "grid": grid,
        "g0_bad_cells": g0_bad,
        "g0_max_radius": max((x.rad() for x in g0_rows), default=arb(0)).str(12),
        "B_over_delta_on_0_0125": value.str(18),
        "B_over_delta_radius": value.rad().str(12),
        "scope": "nominal truncated series; no K2 promotion",
    }
    return (result, bover) if return_series else result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    ctx.prec = 140
    payload = {"rows": [integrate(t) for t in ("2.90", "3.13")]}
    text = json.dumps(payload, indent=2) + "\n"
    print(text, end="")
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text)
