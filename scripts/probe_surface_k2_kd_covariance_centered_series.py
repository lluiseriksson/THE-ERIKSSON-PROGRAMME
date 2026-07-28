"""Cellwise-centered coefficient series for the KD covariance.

The direct four-global-moment assembly loses cancellation before interval
division.  This variant first forms each cell's conditional means and
conditional covariance, then uses the exact law of total covariance:

  Cov(A,G) = sum_i p_i Cov_i(A,G)
             + sum_i p_i (A_i-Abar)(G_i-Gbar).

It remains a nominal fixed-square stress-point design.
"""

from __future__ import annotations

from flint import arb, arb_series, ctx

import probe_surface_k2_kd_covariance as probe
import probe_surface_k2_kd_covariance_series as direct
from surface_remainder_delta0_centered_series import PREC


GRID_LIST = (12, 24)
COEFFICIENT3_RADIUS_TARGET = arb(1968)


def integrate_cell(grid, i, j):
    width = probe.SIDE/grid
    slo, shi = width*i, width*(i+1)
    alo, ahi = width*j, width*(j+1)
    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    center = probe.kd_covariance_point(
        arb(0),
        probe.T,
        probe.old.sd(sm, 1),
        probe.old.sd(am, 0, 1),
    )
    box = probe.kd_covariance_point(
        arb(0),
        probe.T,
        probe.old.sd(probe.old.hull(slo, shi), 1),
        probe.old.sd(probe.old.hull(alo, ahi), 0, 1),
    )
    area = 4*(shi-slo)*(ahi-alo)
    rows = {}
    for name in probe.NAMES:
        coefficients = []
        for order in range(PREC):
            if name == "weight" and order == 0:
                value = probe.endpoint_weight_cell_mass(
                    probe.T, slo, shi, alo, ahi
                )
            else:
                value = direct.cell_integral_coefficient(
                    center, box, name, order, rx, ry, area
                )
            coefficients.append(value)
        rows[name] = arb_series(coefficients, PREC)
    return rows


def assemble(cells) -> arb_series:
    mass = sum((cell["weight"] for cell in cells),
               arb_series([arb(0)], PREC))
    wa = sum((cell["wa"] for cell in cells),
             arb_series([arb(0)], PREC))
    wg = sum((cell["wg"] for cell in cells),
             arb_series([arb(0)], PREC))
    mean_a, mean_g = wa/mass, wg/mass
    total = arb_series([arb(0)], PREC)
    for cell in cells:
        weight = cell["weight"]
        cell_a = cell["wa"]/weight
        cell_g = cell["wg"]/weight
        conditional = (
            cell["wag"]-cell["wa"]*cell["wg"]/weight
        )
        between = weight*(cell_a-mean_a)*(cell_g-mean_g)
        total += conditional+between
    return 4*total/mass


def run(grid: int) -> arb_series:
    cells = [
        integrate_cell(grid, i, j)
        for i in range(grid)
        for j in range(grid)
    ]
    return assemble(cells)


def main() -> int:
    ctx.prec = probe.ARB_BITS
    heads = direct.exact_heads()
    passed = False
    for grid in GRID_LIST:
        y = run(grid)
        coefficients = y.coeffs()
        overlaps = [
            coefficients[index].overlaps(target)
            for index, target in enumerate(heads)
        ]
        radius3 = arb(coefficients[3].rad())
        print("KD COVARIANCE CENTERED SERIES GRID", grid, flush=True)
        for index, coefficient in enumerate(coefficients[:4]):
            print(
                "Y_COEFFICIENT",
                index,
                coefficient,
                "RADIUS",
                arb(coefficient.rad()),
                "TARGET",
                heads[index],
                "OVERLAP",
                overlaps[index],
                flush=True,
            )
        passed = (
            grid == GRID_LIST[-1]
            and all(coefficient.is_finite() for coefficient in coefficients[:4])
            and all(overlaps)
            and arb(radius3.upper()) < COEFFICIENT3_RADIUS_TARGET
        )
    print(
        "KD COVARIANCE CENTERED SERIES DESIGN "
        + ("PASS" if passed else "FAIL")
        + "; NO K2 PROMOTION",
        flush=True,
    )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
