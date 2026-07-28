"""Centered spatial design probe for the K2 ratio-factorized numerator."""

from __future__ import annotations

import argparse
import json

from flint import arb, arb_series, ctx

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_centered_series import (
    PREC, SDual, add, aq, apply_constant_floor, apply_root2_floor,
    inv, mul, neg, p_over_delta, pm1, relative_polynomial, root2_floor,
    sd, sqrt, exp,
)


NAMES = ("gd", "df", "gf", "dd")


def shift_series(value: arb_series) -> arb_series:
    coeffs = value.coeffs()
    if not coeffs[0].contains(arb(0)):
        raise ValueError(f"g constant coefficient does not contain zero: {coeffs[0]}")
    coeffs[0] = arb(0)
    return arb_series(coeffs[1:] + [arb(0)], PREC)


def shift_dual(value: SDual) -> SDual:
    return SDual(*(shift_series(item) for item in value.__dict__.values()))


def ratio_factor_duals(base, t, sigma, tau):
    delta = sd(arb_series([base, arb(1)], PREC))
    p, q = p_over_delta(base, sigma), p_over_delta(base, tau)
    c = (t / 4).cos()
    c2, cc = c**2, 2*c**2-1
    w = add(add(p, q), mul(-1/c2, mul(delta, mul(p, q))))
    radicand = add(1, neg(mul(delta, w)))
    radicand = SDual(apply_root2_floor(radicand.v), radicand.x,
                     radicand.y, radicand.xx, radicand.xy, radicand.yy)
    root = sqrt(radicand)
    root = SDual(apply_constant_floor(root.v, root2_floor().sqrt()),
                 root.x, root.y, root.xx, root.xy, root.yy)
    phase = mul(-4*c, mul(w, inv(add(1, root))))
    h = mul(delta, inv(mul(4*c, root)))
    dw = mul(2, add(1, neg(mul(delta, add(p, q)))))
    bracket = add(
        add(add(mul(-2*cc, mul(delta, p)), mul(-cc, mul(delta, q))),
            2*cc+1),
        add(mul(2, mul(mul(delta, delta), mul(p, q))),
            add(neg(mul(delta, p)), neg(mul(2, mul(delta, q))))))
    fo = mul(-4, mul(p, bracket))
    common = 1/(2*arb.pi()).sqrt()
    root_half = sqrt(root)
    hregular = mul(common/(4*c)**(arb(5)/2),
                   mul(mul(mul(inv(root), inv(root)),
                             inv(root_half)),
                       relative_polynomial(h, "B")))
    hh = mul(hregular, exp(phase))
    ratio = mul(8*c, mul(root, mul(relative_polynomial(h, "A"),
                                   inv(relative_polynomial(h, "B")))))
    r0 = 8*c*aq(relative_coefficients("A", 4)[0]) \
        / aq(relative_coefficients("B", 4)[0])
    g = add(ratio, mul(-r0/2, dw))
    go = shift_dual(g)
    return {
        "gd": mul(mul(hh, dw), go),
        "df": mul(mul(hh, dw), fo),
        "gf": mul(mul(hh, fo), go),
        "dd": mul(mul(hh, dw), dw),
    }, g


def coeff(value, order):
    values = value.coeffs()
    return values[order] if order < len(values) else arb(0)


def centered_cell(base, t, slo, shi, alo, ahi):
    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    center, _ = ratio_factor_duals(base, t, sd(sm, 1), sd(am, 0, 1))
    box, gbox = ratio_factor_duals(base, t, sd(hull(slo, shi), 1),
                                   sd(hull(alo, ahi), 0, 1))
    area = 4*(shi-slo)*(ahi-alo)
    rows = {}
    for name in NAMES:
        row = []
        for order in range(PREC):
            error = (arb(abs(coeff(box[name].xx, order).upper()))*rx**2/2
                     + arb(abs(coeff(box[name].xy, order).upper()))*rx*ry
                     + arb(abs(coeff(box[name].yy, order).upper()))*ry**2/2)
            row.append(area*(coeff(center[name].v, order)+error*pm1()))
        rows[name] = row
    g0 = [gbox.v.coeffs()[0], gbox.x.coeffs()[0], gbox.y.coeffs()[0],
          gbox.xx.coeffs()[0], gbox.xy.coeffs()[0], gbox.yy.coeffs()[0]]
    return rows, g0


def integrate(t_text, grid):
    t = arb(t_text)
    width = arb(12)/grid
    totals = {name: [arb(0) for _ in range(PREC)] for name in NAMES}
    g0_bad = 0
    g0_radius = arb(0)
    for i in range(grid):
        for j in range(grid):
            rows, g0 = centered_cell(arb(0), t, width*i, width*(i+1),
                                     width*j, width*(j+1))
            for item in g0:
                g0_radius = max(g0_radius, item.rad())
                if not item.contains(arb(0)):
                    g0_bad += 1
            for name, row in rows.items():
                for order, value in enumerate(row):
                    totals[name][order] += value
    moments = {name: arb_series(row, PREC) for name, row in totals.items()}
    b_over = moments["gd"]*moments["df"] - moments["gf"]*moments["dd"]
    lane = hull(arb(0), arb("0.0125"))
    value = arb(0)
    for item in reversed(b_over.coeffs()):
        value = value*lane + item
    return {
        "t": t_text,
        "grid": grid,
        "g0_bad_components": g0_bad,
        "g0_max_radius": g0_radius.str(12),
        "B_over_delta_nominal": value.str(18),
        "B_over_delta_radius": value.rad().str(12),
        "scope": "centred spatial nominal design; no K2 promotion",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    ctx.prec = 140
    payload = {"rows": [integrate(t, g) for t in ("2.90", "3.13")
                         for g in (12, 24)]}
    text = json.dumps(payload, indent=2) + "\n"
    print(text, end="")
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text)
