"""Nominal covariance decomposition probe for the K2 factorized bilinear."""

from __future__ import annotations

from fractions import Fraction

from flint import arb, arb_series, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_centered_series import (
    PREC, SDual, add, aq, apply_constant_floor, apply_root2_floor,
    inv, mul, neg, p_over_delta, relative_polynomial, root2_floor,
    sd, sqrt, exp,
)
from surface_bessel_integral_remainder import relative_coefficients


NAMES = ("weight", "wa", "wb", "wab")
GRID_LIST = (12, 24)
SIDE = arb(12)
T = arb("2.90")
ARB_BITS = 140


def shift_series(value: arb_series) -> arb_series:
    coeffs = value.coeffs()
    if not coeffs[0].contains(arb(0)):
        raise ValueError("g constant coefficient does not contain zero")
    coeffs[0] = arb(0)
    return arb_series(coeffs[1:] + [arb(0)], PREC)


def shift_dual(value: SDual) -> SDual:
    return SDual(*(shift_series(item) for item in value.__dict__.values()))


def ratio_factor_point(base, t, sigma, tau):
    delta = sd(arb_series([base, arb(1)], PREC))
    p, q = p_over_delta(base, sigma), p_over_delta(base, tau)
    c = (t/4).cos(); c2, cc = c**2, 2*c**2-1
    w = add(add(p, q), mul(-1/c2, mul(delta, mul(p, q))))
    root = sqrt(SDual(apply_root2_floor(
        add(1, neg(mul(delta, w))).v),
        add(1, neg(mul(delta, w))).x,
        add(1, neg(mul(delta, w))).y,
        add(1, neg(mul(delta, w))).xx,
        add(1, neg(mul(delta, w))).xy,
        add(1, neg(mul(delta, w))).yy))
    root = SDual(apply_constant_floor(root.v, root2_floor().sqrt()),
                 root.x, root.y, root.xx, root.xy, root.yy)
    phase = mul(-4*c, mul(w, inv(add(1, root))))
    h = mul(delta, inv(mul(4*c, root)))
    d = mul(2, add(1, neg(mul(delta, add(p, q)))))
    bracket = add(
        add(add(mul(-2*cc, mul(delta, p)), mul(-cc, mul(delta, q))),
            2*cc+1),
        add(mul(2, mul(mul(delta, delta), mul(p, q))),
            add(neg(mul(delta, p)), neg(mul(2, mul(delta, q))))))
    f = mul(-4, mul(p, bracket))
    common = 1/(2*arb.pi()).sqrt()
    hh = mul(common/(4*c)**(arb(5)/2),
             mul(mul(mul(inv(root), inv(root)), inv(sqrt(root))),
                 relative_polynomial(h, "B")))
    H = mul(hh, exp(phase))
    ratio = mul(8*c, mul(root, mul(relative_polynomial(h, "A"),
                                  inv(relative_polynomial(h, "B")))))
    r0 = 8*c*aq(relative_coefficients("A", 4)[0]) \
        / aq(relative_coefficients("B", 4)[0])
    g_over = shift_dual(add(ratio, mul(-r0/2, d)))
    a = mul(g_over, inv(d))
    b = mul(f, inv(d))
    weight = mul(H, mul(d, d))
    return {
        "weight": weight,
        "wa": mul(weight, a),
        "wb": mul(weight, b),
        "wab": mul(mul(weight, a), b),
        "a": a,
        "b": b,
    }


def coeff(value, order=0):
    values = value.coeffs()
    return values[order] if order < len(values) else arb(0)


def cell_integral(center, box, name, rx, ry, area):
    c = coeff(center[name].v)
    rem = (arb(coeff(box[name].xx).abs_upper())*rx**2/2
           + arb(coeff(box[name].xy).abs_upper())*rx*ry
           + arb(coeff(box[name].yy).abs_upper())*ry**2/2)
    return area*(c+rem*arb("0 +/- 1"))


def run(grid: int):
    width = SIDE/grid
    rows = []
    for i in range(grid):
        for j in range(grid):
            slo, shi = width*i, width*(i+1)
            alo, ahi = width*j, width*(j+1)
            sm, am = (slo+shi)/2, (alo+ahi)/2
            rx, ry = (shi-slo)/2, (ahi-alo)/2
            center = ratio_factor_point(arb(0), T, sd(sm, 1), sd(am, 0, 1))
            box = ratio_factor_point(arb(0), T,
                                     sd(hull(slo, shi), 1),
                                     sd(hull(alo, ahi), 0, 1))
            area = 4*(shi-slo)*(ahi-alo)
            m = {name: cell_integral(center, box, name, rx, ry, area)
                 for name in NAMES}
            rows.append((m, center, box, rx, ry))
    M = sum((m["weight"] for m, *_ in rows), arb(0))
    Sa = sum((m["wa"] for m, *_ in rows), arb(0))
    Sb = sum((m["wb"] for m, *_ in rows), arb(0))
    Abar = Sa/M; Bbar = Sb/M
    between = arb(0); within = arb(0)
    for m, center, box, rx, ry in rows:
        abar = m["wa"]/m["weight"]
        bbar = m["wb"]/m["weight"]
        between += m["weight"]*(abar-Abar)*(bbar-Bbar)
        # First-derivative oscillations of a and b over the cell.
        da = (arb(coeff(box["a"].x).abs_upper())*rx
              + arb(coeff(box["a"].y).abs_upper())*ry)
        db = (arb(coeff(box["b"].x).abs_upper())*rx
              + arb(coeff(box["b"].y).abs_upper())*ry)
        within += m["weight"]*da*db/4
    bound = -M*(between + arb("0 +/- 1")*within)
    return M, Sa, Sb, between, within, bound


def main():
    ctx.prec = ARB_BITS
    for grid in GRID_LIST:
        M, Sa, Sb, between, within, bound = run(grid)
        print("COVARIANCE GRID", grid, "M", M, "between", between,
              "within_radius", within, "B_over_delta", bound,
              "B_radius", arb(bound.rad()), flush=True)
    print("COVARIANCE NOMINAL DESIGN ONLY; NO K2 PROMOTION", flush=True)


if __name__ == "__main__":
    main()
