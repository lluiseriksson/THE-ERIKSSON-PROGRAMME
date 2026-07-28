"""Explicit polynomial rederivation of the low-order K2 coefficients.

No ``sympy.series`` call is used. Every delta operation is a finite list
recurrence, followed by exact Gaussian moment evaluation. This remains a
formal plane-carrier design brick until finite-box and tail charges are added.
"""

from __future__ import annotations

import json
import argparse
from fractions import Fraction
from math import factorial

import sympy as sp

from surface_bessel_integral_remainder import relative_coefficients


ORDER = 4
d, c, sigma, tau = sp.symbols("delta c sigma tau", positive=True)


def zero():
    return [sp.Integer(0)] * (ORDER + 1)


def const(value):
    out = zero(); out[0] = sp.expand(value); return out


def add(a, b):
    return [sp.expand(x + y) for x, y in zip(a, b)]


def neg(a):
    return [sp.expand(-x) for x in a]


def scale(a, value):
    return [sp.expand(value*x) for x in a]


def mul(a, b):
    out = zero()
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j <= ORDER:
                out[i+j] += x*y
    return [sp.expand(x) for x in out]


def reciprocal(a):
    a0 = sp.factor(a[0])
    if a0 == 0:
        raise ValueError("reciprocal has zero leading term")
    out = zero(); out[0] = 1/a0
    for n in range(1, ORDER + 1):
        out[n] = sp.expand(-sum(a[k]*out[n-k] for k in range(1, n+1))/a0)
    return out


def power_one_plus(u, alpha):
    out = const(1); power = const(1); coeff = sp.Integer(1)
    for n in range(1, ORDER + 1):
        power = mul(power, u)
        coeff *= (alpha - (n-1)) / n
        out = add(out, scale(power, coeff))
    return out


def exp_zero_constant(u):
    if sp.simplify(u[0]) != 0:
        raise ValueError("exp_zero_constant expects zero constant")
    out = const(1); power = const(1)
    for n in range(1, ORDER + 1):
        power = mul(power, u)
        out = add(out, scale(power, sp.Rational(1, factorial(n))))
    return out


def poly_horner(h, family):
    out = zero()
    for coeff in reversed(relative_coefficients(family, 4)):
        out = add(mul(out, h), const(Fraction(coeff.numerator, coeff.denominator)))
    return out


def gaussian_expectation(expr):
    total = 0
    for (i, j), coeff in sp.Poly(sp.expand(expr), sigma, tau).terms():
        if i % 2 or j % 2:
            continue
        mi = sp.factorial2(i-1)/c**(i//2) if i else 1
        mj = sp.factorial2(j-1)/c**(j//2) if j else 1
        total += coeff*mi*mj
    return sp.factor(total)


def divide(a, b):
    b0 = sp.factor(b[0]); out = zero()
    for n in range(ORDER + 1):
        out[n] = sp.expand((a[n] - sum(b[k]*out[n-k]
                                        for k in range(1, n+1)))/b0)
    return out


def derive():
    s2, t2 = sigma**2, tau**2
    p = [sp.Integer(0)]*(ORDER+1); q = [sp.Integer(0)]*(ORDER+1)
    for n in range(ORDER+1):
        coeff = sp.Rational((-1)**n*2**(2*n+1), factorial(2*n+2))
        p[n] = coeff*s2/4*(s2/4)**n
        q[n] = coeff*t2/4*(t2/4)**n
    delta = [0, 1, 0, 0, 0]
    w = add(add(p, q), scale(mul(delta, mul(p, q)), -1/c**2))
    root = power_one_plus(scale(mul(delta, w), -1), sp.Rational(1, 2))
    phase = mul(scale(mul(const(c), w), -4), reciprocal(add(const(1), root)))
    phase0 = const(phase[0])
    exp_correction = exp_zero_constant(add(phase, neg(phase0)))
    h = scale(mul(delta, reciprocal(root)), 1/(4*c))
    a_rel, b_rel = poly_horner(h, "A"), poly_horner(h, "B")
    root_m32 = power_one_plus(add(root, const(-1)), sp.Rational(-3, 2))
    root_m52 = power_one_plus(add(root, const(-1)), sp.Rational(-5, 2))
    dw = add(const(2), scale(mul(delta, add(p, q)), -2))
    cc = 2*c**2 - 1
    bracket = add(add(add(scale(mul(delta, p), -2*cc),
                              scale(mul(delta, q), -cc)), const(2*cc+1)),
                   add(scale(mul(mul(delta, delta), mul(p, q)), 2),
                       add(scale(mul(delta, p), -1),
                           scale(mul(delta, q), -2))))
    fo = scale(mul(p, bracket), -4)
    integrands = {
        "kd": mul(mul(root_m32, a_rel), mul(dw, exp_correction)),
        "kf": mul(mul(root_m32, a_rel), mul(fo, exp_correction)),
        "hdd": mul(mul(root_m52, b_rel), mul(mul(dw, dw), exp_correction)),
        "hdf": mul(mul(root_m52, b_rel), mul(mul(dw, fo), exp_correction)),
    }
    moments = {name: [gaussian_expectation(value[k])
                      for k in range(ORDER+1)]
               for name, value in integrands.items()}
    kd, kf = moments["kd"], moments["kf"]
    hdd, hdf = moments["hdd"], moments["hdf"]
    bilinear = [sp.factor(sum(kd[j]*hdf[n-j]-kf[j]*hdd[n-j]
                              for j in range(n+1)))
                for n in range(ORDER+1)]
    if sp.simplify(bilinear[0]) != 0:
        raise AssertionError(f"formal B0 did not cancel: {bilinear[0]}")
    b_shift = bilinear[1:] + [sp.Integer(0)]
    denominator = scale(mul(const(c), mul(kd, kd)), 2)
    y = [sp.factor(value) for value in divide(b_shift, denominator)]
    targets = [
        (4*c**2-1)/(8*c**3),
        (-8*c**4+15*c**2-4)/(32*c**6),
        -(12*c**6+485*c**4-796*c**2+224)/(1024*c**9),
        (28*c**8+41*c**6-1464*c**4+1856*c**2-500)/(1024*c**12),
    ]
    checks = [sp.simplify(y[i]-targets[i]) for i in range(4)]
    if any(value != 0 for value in checks):
        raise AssertionError(f"closed coefficient mismatch: {checks}")
    return {"B0": bilinear[0], "coefficients": y, "checks": checks,
            "moments": moments}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    result = derive()
    text = json.dumps({"B0": str(result["B0"]),
                       "coefficients": [str(x) for x in result["coefficients"]],
                       "checks": [str(x) for x in result["checks"]],
                       "moment_constants": {
                           name: str(values[0])
                           for name, values in result["moments"].items()
                       },
                       "scope": "formal plane carrier; no K2 promotion"},
                      indent=2) + "\n"
    print(text, end="")
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text)
