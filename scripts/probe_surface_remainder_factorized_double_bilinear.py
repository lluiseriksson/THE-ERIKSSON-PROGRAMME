"""Midpoint algebra check for the corrected K2 double-bilinear factorization.

This is not an interval certificate.  It verifies, on a tiny midpoint grid,
that the exact product-of-sums bilinear equals the factorized double sum
using r=K/H.  The check is deliberately independent of the diagonal probe.
"""

from __future__ import annotations

import argparse
import json

from flint import arb, ctx

from surface_remainder_delta0_series_design import sinc2_derivatives
from surface_bessel_integral_remainder import relative_coefficients


def rel_poly(h, family):
    out = arb(0)
    for coeff in reversed(relative_coefficients(family, 4)):
        out = out * h + arb(str(coeff))
    return out


def point_factors(t, delta, sigma, tau):
    p = sigma**2 / 4 * sinc2_derivatives(delta * sigma**2 / 4, 0)[0]
    q = tau**2 / 4 * sinc2_derivatives(delta * tau**2 / 4, 0)[0]
    c = (t / 4).cos()
    c2 = c**2
    cc = 2 * c2 - 1
    w = p + q - delta * p * q / c2
    root = (1 - delta * w).sqrt()
    phase = -4 * c * w / (1 + root)
    h = delta / (4 * c * root)
    dw = 2 * (1 - delta * (p + q))
    bracket = (-2 * cc * delta * p - cc * delta * q + 2 * cc + 1
               + 2 * delta**2 * p * q - delta * p - 2 * delta * q)
    fo = -4 * p * bracket
    common = 1 / (2 * arb.pi()).sqrt()
    e = phase.exp()
    k = (2 * common / (4 * c)**(arb(3) / 2)
         * root**(-arb(3) / 2) * rel_poly(h, "A") * e)
    hh = (common / (4 * c)**(arb(5) / 2)
          * root**(-arb(5) / 2) * rel_poly(h, "B") * e)
    return k, hh, dw, fo


def run_case(t_text, delta_text, grid=2):
    t, delta = arb(t_text), arb(delta_text)
    width = arb(12) / grid
    cells = []
    for i in range(grid):
        for j in range(grid):
            sigma = width * (i + arb("0.5"))
            tau = width * (j + arb("0.5"))
            k, hh, d, f = point_factors(t, delta, sigma, tau)
            cells.append((k, hh, d, f))
    area = 4 * width**2
    kd = sum((area * k * d for k, hh, d, f in cells), arb(0))
    kf = sum((area * k * f for k, hh, d, f in cells), arb(0))
    hdd = sum((area * hh * d**2 for k, hh, d, f in cells), arb(0))
    hdf = sum((area * hh * d * f for k, hh, d, f in cells), arb(0))
    product = kd * hdf - kf * hdd
    factored = arb(0)
    for k, hh, d, f in cells:
        r = k / hh
        for kp, hhp, dp, fp in cells:
            rp = kp / hhp
            factored += (area**2 / 2 * hh * hhp
                         * (d * fp - f * dp) * (r * dp - rp * d))
    return {
        "t": t_text,
        "delta": delta_text,
        "product_B0": product.str(18),
        "factorized_B0": factored.str(18),
        "difference": (product - factored).str(18),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    ctx.prec = 120
    payload = {
        "rows": [run_case(t, d) for t in ("2.90", "3.13")
                 for d in ("0", "0.001", "0.0125")],
        "scope": "midpoint algebra audit; no K2 promotion",
    }
    text = json.dumps(payload, indent=2) + "\n"
    print(text, end="")
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text)
