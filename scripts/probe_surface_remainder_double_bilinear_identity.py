"""Cheap design-only falsification of the cell-diagonal K2 bilinear.

This uses midpoint samples, not certified spatial integration.  It checks the
algebraic distinction between the diagonal cell sum and the production
product-of-sums before any long run is attempted.
"""

from __future__ import annotations

import json
import argparse

from flint import arb, arb_series, ctx

from surface_remainder_delta0_series_design import nominal_moment_series


NAMES = ("kd", "kf", "hdd", "hdf")
PREC = 6


def point_bilinears(t: arb, base: arb, grid: int = 2):
    side = arb(12)
    width = side / grid
    diag = [arb(0) for _ in range(PREC)]
    totals = {name: [arb(0) for _ in range(PREC)] for name in NAMES}
    for i in range(grid):
        for j in range(grid):
            sigma = width * (i + arb("0.5"))
            tau = width * (j + arb("0.5"))
            values = nominal_moment_series(base, t, sigma, tau, PREC)
            area = 4 * width**2
            local = values["kd"] * values["hdf"] - values["kf"] * values["hdd"]
            for k, value in enumerate(local.coeffs()):
                diag[k] += area * value
            for name in NAMES:
                for k, value in enumerate(values[name].coeffs()):
                    totals[name][k] += area * value
    sums = {name: arb_series(values, PREC) for name, values in totals.items()}
    prod = sums["kd"] * sums["hdf"] - sums["kf"] * sums["hdd"]
    return arb_series(diag, PREC), prod


def run():
    ctx.prec = 120
    rows = []
    for t_text in ("2.90", "3.13"):
        for delta_text in ("0", "0.001", "0.0125"):
            diag, prod = point_bilinears(arb(t_text), arb(delta_text))
            diff = diag - prod
            rows.append({
                "t": t_text,
                "delta": delta_text,
                "diag_B0": diag.coeffs()[0].str(18),
                "prod_B0": prod.coeffs()[0].str(18),
                "difference_B0": diff.coeffs()[0].str(18),
                "difference_midpoint": diff.coeffs()[0].mid().str(18),
            })
    return rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    payload = {"rows": run(), "scope": "design-only; no K2 promotion"}
    text = json.dumps(payload, indent=2) + "\n"
    print(text, end="")
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text)
