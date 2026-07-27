"""Exploratory G5 point-cell probe with a wider central q window.

This file is design evidence only.  It cannot emit a production
certificate and does not cover a parameter union.
"""

from __future__ import annotations

import argparse
from fractions import Fraction

from flint import arb, ctx

import certify_surface_high_beta_g5_local_tail_18_5 as old
from surface_right_edge_five_family_ratio_design import assemble_ratio


SIDE = arb(4)
COARSE_QGRID = 128
MIXED_QGRID = 256
DELTA_MAX = Fraction(9, 1000)
LAMBDA_MAX = Fraction(18, 5)


def near_bounds(delta_max: arb, lambda_hi: arb):
    saved = old.central.reduced_values
    old.central.reduced_values = old.finite_tail.low_argument_companion
    try:
        delta = old.hull(arb(0), delta_max)
        v = old.hull(old.finite_tail.VMIN, arb(2))
        i0, i1 = old.finite_tail.low_argument_companion(delta / v, v)
        gaussian = (
            4
            * lambda_hi.exp()
            * old.halfline_tail.gaussian_one_side(arb(4) / 3, SIDE)
        )
        u, b = {}, {}
        for order, weight in (
            (1, 2 / arb.pi()),
            (3, 1 / (3 * arb.pi())),
            (5, 1 / (30 * arb.pi())),
        ):
            u[order] = (
                gaussian
                * weight
                * arb(i1.abs_upper())
                * arb(
                    old.finite_tail.chain(
                        "I1", order, delta_max=delta_max
                    ).abs_upper()
                )
                / 4
            )
        for order, weight in (
            (2, 1 / arb.pi()),
            (4, 2 / (3 * arb.pi())),
        ):
            b[order] = (
                gaussian
                * weight
                * arb(i0.abs_upper())
                * arb(
                    old.finite_tail.chain(
                        "I0", order, arb(1) / 2, delta_max=delta_max
                    ).abs_upper()
                )
            )
        return u, b
    finally:
        old.central.reduced_values = saved


def budgets(delta_max: arb, lambda_hi: arb):
    near_u, near_b = near_bounds(delta_max, lambda_hi)
    far_u, far_b = old.finite_tail.far_bounds(delta_max)
    return (
        near_u[1] + far_u[1],
        near_u[3] + far_u[3],
        near_u[5] + far_u[5],
        near_b[2] + far_b[2],
        near_b[4] + far_b[4],
    )


def install_side4_backend(delta_max: arb, lambda_hi: arb) -> None:
    """Install only floors proved for the wider chart."""

    old.beta20.install(delta_max)
    endpoint = arb(delta_max.upper())
    angle = (
        arb.pi() / 4
        - SIDE * endpoint.sqrt()
        - lambda_hi * endpoint / 4
    )
    value_floor = 2 * angle.sin()
    if not value_floor > 0:
        raise AssertionError("side-four Bessel value floor is unresolved")
    old.beta20.ACTIVE_VALUE_FLOOR = value_floor
    old.beta20.ACTIVE_INVZ_CEILING = endpoint / value_floor
    if not old.beta20.ACTIVE_INVZ_CEILING < arb(1) / 4:
        raise AssertionError("side-four inverse-z ceiling is unresolved")


def verify_geometry() -> None:
    delta = old.aq(DELTA_MAX)
    shift = old.aq(DELTA_MAX * LAMBDA_MAX / 2)
    alpha = arb(7) / 50
    assert SIDE * delta.sqrt() < arb.pi() / 4 - alpha - shift / 2
    assert 2 * (alpha - shift).sin() > old.finite_tail.VMIN
    amplitude = (2 - 2 * shift.sin()).sqrt()
    sinc_floor = 1 - delta * SIDE**2 / 24
    assert amplitude * sinc_floor**2 > arb(4) / 3
    assert delta / old.finite_tail.VMIN < arb(1) / 4
    old.finite_tail.verify_geometry()


def judge_box(
    dlo: Fraction,
    dhi: Fraction,
    llo: Fraction,
    lhi: Fraction,
):
    delta = old.hull(old.aq(dlo), old.aq(dhi))
    lam = old.hull(old.aq(llo), old.aq(lhi))
    install_side4_backend(old.aq(dhi), old.aq(lhi))
    charges = budgets(old.aq(dhi), old.aq(lhi))

    def enlarge(row):
        return tuple(
            value + charge * arb("0 +/- 1")
            for value, charge in zip(row, charges)
        )

    values = old.central.central_families(
        delta, lam, side=SIDE, qgrid=COARSE_QGRID, rgrid=16,
        thetagrid=4, phigrid=4,
    )
    families = enlarge(values)
    p0, h = old.central.assemble_h(delta, lam, families)
    ratio, ratio_b0 = assemble_ratio(delta, lam, families)
    assert ratio_b0.overlaps(families[3])
    resolution = "coarse-ratio"
    if not (
        families[3].lower() > 0
        and ratio.lower() > 0
    ):
        values = (
            old.central.integrate_u_family(
                delta, lam, 1, side=SIDE, qgrid=MIXED_QGRID, rgrid=32,
                thetagrid=4, phigrid=1,
            ),
            old.central.integrate_u_family(
                delta, lam, 3, side=SIDE, qgrid=MIXED_QGRID, rgrid=32,
                thetagrid=8, phigrid=1,
            ),
            old.central.integrate_u_family(
                delta, lam, 5, side=SIDE, qgrid=MIXED_QGRID, rgrid=32,
                thetagrid=4, phigrid=1,
            ),
            old.central.integrate_b_family(
                delta, lam, 2, side=SIDE, qgrid=MIXED_QGRID, rgrid=32,
                thetagrid=1,
            ),
            old.central.integrate_b_family(
                delta, lam, 4, side=SIDE, qgrid=MIXED_QGRID, rgrid=32,
                thetagrid=8,
            ),
        )
        families = enlarge(values)
        p0, h = old.central.assemble_h(delta, lam, families)
        ratio, ratio_b0 = assemble_ratio(delta, lam, families)
        assert ratio_b0.overlaps(families[3])
        resolution = "mixed-ratio"
    return resolution, charges, families, p0, h, ratio


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lambda-index", type=int, required=True)
    parser.add_argument("--delta-index", type=int, default=0)
    parser.add_argument("--lambda-parts", type=int, default=1)
    parser.add_argument("--lambda-part", type=int, default=0)
    parser.add_argument("--delta-parts", type=int, default=1)
    parser.add_argument("--delta-part", type=int, default=0)
    parser.add_argument("--side", choices=("5/2", "4"), default="4")
    args = parser.parse_args()
    if not 100 <= args.lambda_index < 180:
        raise ValueError("lambda index outside probe range")
    if not 0 <= args.delta_index < 9:
        raise ValueError("delta index outside probe range")
    if not 0 <= args.lambda_part < args.lambda_parts:
        raise ValueError("lambda subpart outside probe range")
    if not 0 <= args.delta_part < args.delta_parts:
        raise ValueError("delta subpart outside probe range")
    global SIDE, COARSE_QGRID, MIXED_QGRID
    if args.side == "5/2":
        SIDE = arb(5) / 2
        COARSE_QGRID = 80
        MIXED_QGRID = 160
    else:
        SIDE = arb(4)
        COARSE_QGRID = 128
        MIXED_QGRID = 256
    ctx.prec = 140
    verify_geometry()
    lambda_parent_lo = Fraction(args.lambda_index, 50)
    lambda_width = Fraction(1, 50 * args.lambda_parts)
    llo = lambda_parent_lo + args.lambda_part * lambda_width
    lhi = llo + lambda_width
    delta_parent_lo = Fraction(args.delta_index, 1000)
    delta_width = Fraction(1, 1000 * args.delta_parts)
    dlo = delta_parent_lo + args.delta_part * delta_width
    dhi = dlo + delta_width
    resolution, charges, families, p0, h, ratio = judge_box(
        dlo, dhi, llo, lhi
    )
    print("DESIGN PROBE ONLY; NOT A CERTIFICATE")
    print("side", args.side, "qgrids", COARSE_QGRID, MIXED_QGRID)
    print("box", dlo, dhi, llo, lhi)
    print("resolution", resolution)
    print("tail_upper", *(arb(x.upper()).str(30) for x in charges))
    print("B0_lower", arb(families[3].lower()).str(50))
    print("P0_lower", arb(p0.lower()).str(50))
    print("H_lower", arb(h.lower()).str(50))
    print("ratio_Q_lower", arb(ratio.lower()).str(50))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
