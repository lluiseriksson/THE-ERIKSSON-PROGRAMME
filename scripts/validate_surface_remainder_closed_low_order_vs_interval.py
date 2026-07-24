"""Compare formal Gaussian low-order moments with interval boxes.

This is an independent consistency check only.  The formal values are full
plane carriers; the interval integrator covers the finite positive quadrant
with symmetry, so the comparison is expected to contain a small complement
tail and never certifies K2.
"""

from __future__ import annotations

import argparse
import json
import sympy as sp
from flint import arb, arb_series, ctx

from surface_remainder_delta0_closed_low_order import c as c_symbol, derive
from surface_remainder_delta0_series_design import integrate_coefficients


def formal_arb(expr, c_value):
    value = sp.N(expr.subs(c_symbol, c_value), 90)
    return arb(str(value))


def run(t_text="2.90", grid=24):
    ctx.prec = 140
    t_arb = arb(t_text)
    c_arb = (t_arb/4).cos()
    c_sym = sp.N(sp.cos(sp.Rational(t_text)/4), 90)
    payload = derive()
    # The closed script omits the common Gaussian and kernel prefactors.
    mass = 2*arb.pi()/c_arb
    common = 1/(2*arb.pi()).sqrt()
    scale_k = 2*common/(4*c_arb)**(arb(3)/2)*mass
    scale_h = common/(4*c_arb)**(arb(5)/2)*mass
    vals = integrate_coefficients(t_arb, grid=grid, base=arb(0))
    intervals = {name: arb_series(row, 6) for name, row in vals.items()}
    failures = []
    checks = []
    for name, scale in (("kd", scale_k), ("kf", scale_k),
                        ("hdd", scale_h), ("hdf", scale_h)):
        for order in range(4):
            expected = formal_arb(payload["moments"][name][order], c_sym)*scale
            got = intervals[name].coeffs()[order]
            ok = got.contains(expected)
            checks.append({"name": name, "order": order,
                           "expected": expected.str(16),
                           "interval": got.str(16), "contains": ok})
            if not ok:
                failures.append((name, order))
    return {"checks": checks, "failures": failures,
            "scope": "formal full-plane vs finite-box interval; no K2 promotion"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--t", default="2.90")
    parser.add_argument("--grid", type=int, default=24)
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    result = run(args.t, args.grid)
    for row in result["checks"]:
        print(row)
    print("CLOSED LOW-ORDER MOMENT CONTAINMENT",
          "PASS" if not result["failures"] else "FAIL")
    print(result["scope"])
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            json.dump(result, handle, indent=2, default=str)
            handle.write("\n")
    if result["failures"]:
        raise SystemExit(1)
