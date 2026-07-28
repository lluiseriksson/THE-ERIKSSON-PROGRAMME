"""Coefficientwise KD-covariance probe at the K2 endpoint stress point.

This integrates the four series ``weight``, ``weight*A``, ``weight*G`` and
``weight*A*G`` cellwise, then forms the exact formal identity

    Y = 4 * (E[A*G] - E[A]*E[G]).

Only the nominal fixed square is present.  Companion and exterior charges,
the full t-cover, and a positive-delta remainder are deliberately absent.
"""

from __future__ import annotations

from flint import arb, arb_series, ctx

import probe_surface_k2_kd_covariance as probe
from surface_remainder_delta0_centered_series import PREC


GRID_LIST = (12, 24)
COEFFICIENT3_RADIUS_TARGET = arb(1968)


def cell_integral_coefficient(center, box, name, order, rx, ry, area):
    value = probe.old.coeff(center[name].v, order)
    remainder = (
        arb(probe.old.coeff(box[name].xx, order).abs_upper()) * rx**2 / 2
        + arb(probe.old.coeff(box[name].xy, order).abs_upper()) * rx * ry
        + arb(probe.old.coeff(box[name].yy, order).abs_upper()) * ry**2 / 2
    )
    return area * (value + remainder * arb("0 +/- 1"))


def run(grid: int) -> arb_series:
    width = probe.SIDE / grid
    totals = {
        name: [arb(0) for _ in range(PREC)]
        for name in probe.NAMES
    }
    for i in range(grid):
        for j in range(grid):
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
            for name in probe.NAMES:
                for order in range(PREC):
                    if name == "weight" and order == 0:
                        value = probe.endpoint_weight_cell_mass(
                            probe.T, slo, shi, alo, ahi
                        )
                    else:
                        value = cell_integral_coefficient(
                            center, box, name, order, rx, ry, area
                        )
                    totals[name][order] += value
    series = {
        name: arb_series(coefficients, PREC)
        for name, coefficients in totals.items()
    }
    mass_inverse = 1 / series["weight"]
    mean_a = series["wa"] * mass_inverse
    mean_g = series["wg"] * mass_inverse
    mean_ag = series["wag"] * mass_inverse
    return 4*(mean_ag-mean_a*mean_g)


def exact_heads():
    from surface_remainder_delta0_fourth_coefficient import target_y3
    from surface_remainder_s2_direct_judge import closed_forms

    leading, r2, r3, _ = closed_forms(probe.T)
    r4 = target_y3((probe.T/4).cos())
    return leading, r2, r3, r4


def main() -> int:
    ctx.prec = probe.ARB_BITS
    heads = exact_heads()
    passed = False
    for grid in GRID_LIST:
        y = run(grid)
        coefficients = y.coeffs()
        overlaps = [
            coefficients[index].overlaps(target)
            for index, target in enumerate(heads)
        ]
        radius3 = arb(coefficients[3].rad())
        print("KD COVARIANCE SERIES GRID", grid, flush=True)
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
        "KD COVARIANCE SERIES DESIGN "
        + ("PASS" if passed else "FAIL")
        + "; NO K2 PROMOTION",
        flush=True,
    )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
