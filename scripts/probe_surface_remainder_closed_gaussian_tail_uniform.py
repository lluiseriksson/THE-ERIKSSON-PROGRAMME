"""Uniform (in a c-box) Gaussian-complement design bound for K2 moments.

This is deliberately a design probe, not a K2 certificate.  Unlike the
midpoint probe, every rational coefficient is evaluated on an Arb interval;
the Gaussian tail and prefactor use the least c in the box.  The script is
useful for exposing whether a t-box can plausibly fit the registered Theta3
budget before a full joint (delta,t) certificate is attempted.
"""

from __future__ import annotations

import argparse
import json
import sympy as sp
from flint import arb, ctx

from surface_remainder_delta0_closed_low_order import c as c_symbol, derive, sigma, tau


L = arb(12)


def eval_poly_interval(expr, variable, x):
    poly = sp.Poly(sp.expand(expr), variable)
    out = arb(0)
    for (power,), coefficient in poly.terms():
        out += arb(str(coefficient)) * x**power
    return out


def eval_coefficient_interval(expr, c_value):
    """Evaluate a rational-in-c coefficient without midpoint substitution."""
    num, den = sp.fraction(sp.together(expr))
    numerator = eval_poly_interval(num, c_symbol, c_value)
    denominator = eval_poly_interval(den, c_symbol, c_value)
    if denominator.contains(0):
        raise ValueError(f"coefficient denominator crosses zero on {c_value}: {expr}")
    return numerator / denominator


def half_moment(order, a):
    if order % 2:
        return arb(0)
    if order == 0:
        return arb.pi().sqrt() / (2 * a.sqrt())
    return arb(order - 1) / (2 * a) * half_moment(order - 2, a)


def tail_upper(order, a):
    if order % 2:
        return arb(0)
    value = (-(a * L**2)).exp() / (2 * a * L)
    for n in range(2, order + 1, 2):
        value = (L ** (n - 1) * (-(a * L**2)).exp() / (2 * a)
                 + arb(n - 1) / (2 * a) * value)
    return value


def polynomial_tail(expr, c_value, a_lower):
    poly = sp.Poly(sp.expand(expr), sigma, tau)
    total = arb(0)
    for (i, j), coefficient in poly.terms():
        if i % 2 or j % 2:
            continue
        coeff = eval_coefficient_interval(coefficient, c_value).abs_upper()
        total += coeff * (tail_upper(i, a_lower) * half_moment(j, a_lower)
                          + half_moment(i, a_lower) * tail_upper(j, a_lower))
    return total


def run(t_lo, t_hi):
    ctx.prec = 160
    t_box = arb(str(t_lo)).union(arb(str(t_hi)))
    c_box = t_box / 4
    c_box = c_box.cos()
    c_lower = c_box.lower()
    a_lower = c_lower / 2
    result = derive()
    common = 1 / (2 * arb.pi()).sqrt()
    pref = {
        "kd": 2 * common / (4 * c_lower) ** (arb(3) / 2),
        "kf": 2 * common / (4 * c_lower) ** (arb(3) / 2),
        "hdd": common / (4 * c_lower) ** (arb(5) / 2),
        "hdf": common / (4 * c_lower) ** (arb(5) / 2),
    }
    rows = []
    for name, values in result["moments"].items():
        for order, expr in enumerate(values):
            raw = polynomial_tail(expr, c_box, a_lower)
            bound = pref[name] * 4 * raw
            rows.append({"name": name, "order": order,
                         "tail_upper": bound.str(18)})
    return {"t_box": [str(t_lo), str(t_hi)], "c_box": c_box.str(20),
            "rows": rows,
            "scope": "uniform c-box Gaussian complement design; no K2 promotion"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-lo", default="2.90")
    parser.add_argument("--t-hi", default="2.91")
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    payload = run(args.t_lo, args.t_hi)
    text = json.dumps(payload, indent=2) + "\n"
    print(text, end="")
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text)
