"""KD-weighted exact covariance probe for the corrected K2 quotient.

With ``dP = K D dx / KD``, ``A=F/D``, and ``R=(H/K)D``,

    B/KD^2 = Cov_P(A,R).

Since ``R(0)=1/(4c)`` is spatially constant, writing
``G=(R-1/(4c))/delta`` gives the removable-singularity identity

    Y = 4 Cov_P(A,G).

This file only tests the conditioning of that exact representation at the
delta-zero stress point.  Companion and outer tails are absent.
"""

from __future__ import annotations

from flint import arb, ctx

import probe_surface_k2_covariance_certificate as old
from surface_remainder_delta0_centered_series import add, inv, mul


NAMES = ("weight", "wa", "wg", "wag")
GRID_LIST = (12, 24)
SIDE = old.SIDE
T = old.T
ARB_BITS = old.ARB_BITS


def endpoint_weight_cell_mass(t, slo, shi, alo, ahi):
    """Exact separated integral of the delta-zero KD density on one cell."""

    c = (t / 4).cos()
    common = 1 / (2 * arb.pi()).sqrt()
    prefactor = 4 * common / (4 * c) ** (arb(3) / 2)
    scale = (c / 2).sqrt()
    integral_scale = (arb.pi() / (2 * c)).sqrt()

    def one_dimensional(lo, hi):
        return integral_scale * (
            (scale * hi).erf() - (scale * lo).erf()
        )

    return (
        4
        * prefactor
        * one_dimensional(slo, shi)
        * one_dimensional(alo, ahi)
    )


def kd_covariance_point(base, t, sigma, tau):
    raw = old.ratio_factor_point(base, t, sigma, tau)
    d, f, ratio, hkernel = (
        raw["d"],
        raw["f"],
        raw["ratio"],
        raw["H"],
    )
    weight = mul(mul(hkernel, ratio), d)
    a = mul(f, inv(d))
    r = mul(d, inv(ratio))
    r_constant = 2 / raw["r0"]
    g = old.shift_dual(add(r, -r_constant))
    return {
        "weight": weight,
        "wa": mul(weight, a),
        "wg": mul(weight, g),
        "wag": mul(mul(weight, a), g),
        "a": a,
        "g": g,
    }


def within_cell_covariance_radius(weight_mass, a_radius, g_radius):
    """Grüss bound from center-deviation radii on one cell.

    If ``|A-A_center|<=a_radius`` and ``|G-G_center|<=g_radius``, their
    ranges have widths at most ``2*a_radius`` and ``2*g_radius``.  Grüss
    therefore gives ``|Cov(A,G)|<=a_radius*g_radius``.
    """

    return weight_mass * a_radius * g_radius


def run(grid: int):
    width = SIDE / grid
    rows = []
    for i in range(grid):
        for j in range(grid):
            slo, shi = width * i, width * (i + 1)
            alo, ahi = width * j, width * (j + 1)
            sm, am = (slo + shi) / 2, (alo + ahi) / 2
            rx, ry = (shi - slo) / 2, (ahi - alo) / 2
            center = kd_covariance_point(
                arb(0), T, old.sd(sm, 1), old.sd(am, 0, 1)
            )
            box = kd_covariance_point(
                arb(0),
                T,
                old.sd(old.hull(slo, shi), 1),
                old.sd(old.hull(alo, ahi), 0, 1),
            )
            area = 4 * (shi - slo) * (ahi - alo)
            moments = {}
            for name in NAMES:
                if name == "weight":
                    moments[name] = endpoint_weight_cell_mass(
                        T, slo, shi, alo, ahi
                    )
                else:
                    moments[name] = old.cell_integral(
                        center, box, name, rx, ry, area
                    )
            rows.append((moments, center, box, rx, ry))
    mass = sum((moments["weight"] for moments, *_ in rows), arb(0))
    if not arb(mass.lower()) > 0:
        raise ValueError("KD covariance mass is not strictly positive")
    mean_a = sum((moments["wa"] for moments, *_ in rows), arb(0)) / mass
    mean_g = sum((moments["wg"] for moments, *_ in rows), arb(0)) / mass
    between = arb(0)
    within = arb(0)
    for moments, center, box, rx, ry in rows:
        a_bar = moments["wa"] / moments["weight"]
        g_bar = moments["wg"] / moments["weight"]
        between += moments["weight"] * (a_bar - mean_a) * (g_bar - mean_g)
        da = (
            arb(old.coeff(box["a"].x).abs_upper()) * rx
            + arb(old.coeff(box["a"].y).abs_upper()) * ry
        )
        dg = (
            arb(old.coeff(box["g"].x).abs_upper()) * rx
            + arb(old.coeff(box["g"].y).abs_upper()) * ry
        )
        within += within_cell_covariance_radius(
            moments["weight"], da, dg
        )
    y = 4 * (between + arb("0 +/- 1") * within) / mass
    return mass, mean_a, mean_g, between, within, y


def main() -> None:
    ctx.prec = ARB_BITS
    target = old.arb(
        (4 * (T / 4).cos() ** 2 - 1) / (8 * (T / 4).cos() ** 3)
    )
    for grid in GRID_LIST:
        mass, mean_a, mean_g, between, within, y = run(grid)
        print(
            "KD COVARIANCE GRID",
            grid,
            "M",
            mass,
            "mean_a",
            mean_a,
            "mean_g",
            mean_g,
            "between",
            between,
            "within_radius",
            within,
            "Y",
            y,
            "Y_radius",
            arb(y.rad()),
            "TARGET_OVERLAP",
            y.is_finite() and y.overlaps(target),
            flush=True,
        )
    print("KD COVARIANCE NOMINAL DESIGN ONLY; NO K2 PROMOTION", flush=True)


if __name__ == "__main__":
    main()
