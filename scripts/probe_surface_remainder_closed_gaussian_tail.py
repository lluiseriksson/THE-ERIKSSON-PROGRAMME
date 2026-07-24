"""Design bound for the Gaussian complement tail of closed K2 coefficients."""

from __future__ import annotations

import json
import argparse
import sympy as sp
from flint import arb, ctx

from surface_remainder_delta0_closed_low_order import c as c_symbol, derive, sigma, tau


L = arb(12)


def coeff_arb(value, c_value):
    return arb(str(sp.N(value.subs(c_symbol, sp.N(c_value.mid(), 90)), 90)))


def full_half_moment(order, a):
    if order % 2:
        return arb(0)
    if order == 0:
        return arb.pi().sqrt()/(2*a.sqrt())
    return arb.pi().sqrt()*arb(1)


def half_moment(order, a):
    # Exact recurrence for even moments on [0,infinity).
    if order % 2:
        return arb(0)
    if order == 0:
        return arb.pi().sqrt()/(2*a.sqrt())
    return arb(order-1)/(2*a)*half_moment(order-2, a)


def tail_upper(order, a):
    # I_0(L) <= exp(-a L^2)/(2 a L); recurrence gives an upper bound.
    if order % 2:
        return arb(0)
    value = (-(a*L**2)).exp()/(2*a*L)
    for n in range(2, order+1, 2):
        value = L**(n-1)*(-(a*L**2)).exp()/(2*a) \
            + arb(n-1)/(2*a)*value
    return value


def polynomial_tail(expr, c_value):
    a = c_value/2
    poly = sp.Poly(sp.expand(expr), sigma, tau)
    total = arb(0)
    for (i, j), coefficient in poly.terms():
        if i % 2 or j % 2:
            continue
        coeff = coeff_arb(coefficient, c_value).abs_upper()
        total += coeff*(tail_upper(i, a)*half_moment(j, a)
                         +half_moment(i, a)*tail_upper(j, a))
    return total


def run():
    ctx.prec = 160
    t = arb("2.90")
    c_value = (t/4).cos()
    result = derive()
    common = 1/(2*arb.pi()).sqrt()
    pref = {
        "kd": 2*common/(4*c_value)**(arb(3)/2),
        "kf": 2*common/(4*c_value)**(arb(3)/2),
        "hdd": common/(4*c_value)**(arb(5)/2),
        "hdf": common/(4*c_value)**(arb(5)/2),
    }
    rows = []
    for name, values in result["moments"].items():
        for order, expr in enumerate(values):
            raw = polynomial_tail(expr, c_value)
            bound = pref[name]*4*raw
            rows.append({"name": name, "order": order,
                         "tail_upper": bound.str(18)})
    return {"rows": rows,
            "scope": "formal Gaussian complement design; no K2 promotion"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    payload = run()
    text = json.dumps(payload, indent=2) + "\n"
    print(text, end="")
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text)
