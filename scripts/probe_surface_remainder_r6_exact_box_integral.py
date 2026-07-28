"""Design probe: exact monomial integration of the regular R6 jet.

The existing endpoint probe encloses high-degree sigma/tau polynomials on
rectangular cells.  Here the same seventh-order nominal jet is expanded
symbolically and every monomial is integrated exactly over [0,12]^2 before
the c=cos(t/4) interval is evaluated.  This is still nominal only: companion
remainders, completion, and spatial tails are deliberately absent.
"""

from fractions import Fraction
from functools import lru_cache
from math import factorial

import sympy as sp
from flint import arb, arb_series, ctx

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_arb_jet2 import hull

N = 7
d, sigma, tau, c = sp.symbols("delta sigma tau c", positive=True)


def zero():
    return [sp.S.Zero] * N


def const(value):
    return [sp.sympify(value)] + [sp.S.Zero] * (N - 1)


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def neg(a):
    return [-x for x in a]


def scale(a, value):
    return [value * x for x in a]


def mul(a, b):
    return [sum(a[k] * b[n-k] for k in range(n + 1))
            for n in range(N)]


def inv(a):
    out = zero()
    out[0] = 1 / a[0]
    for n in range(1, N):
        out[n] = -out[0] * sum(a[k] * out[n-k] for k in range(1, n + 1))
    return out


def sqrt_series(a):
    out = zero()
    out[0] = sp.sqrt(a[0])
    for n in range(1, N):
        out[n] = (a[n] - sum(out[k] * out[n-k] for k in range(1, n))) \
            / (2 * out[0])
    return out


def exp_series(a):
    out = zero()
    out[0] = sp.exp(a[0])
    for n in range(1, N):
        out[n] = sum(k * a[k] * out[n-k] for k in range(1, n + 1)) / n
    return out


def polynomial(a, coefficients):
    out = const(0)
    for coefficient in reversed(coefficients):
        out = add(mul(out, a), const(sp.Rational(
            coefficient.numerator, coefficient.denominator)))
    return out


def integrand_series():
    s2, t2 = sigma**2, tau**2
    unit = [sp.S.Zero, sp.S.One] + [sp.S.Zero] * (N - 2)

    def sinc_square_scaled(x2):
        return [sp.Rational((-1)**n * 2**(2*n + 1), factorial(2*n + 2))
                * x2 / 4 * (x2 / 4)**n for n in range(N)]

    p, q = sinc_square_scaled(s2), sinc_square_scaled(t2)
    w = add(add(p, q), neg(scale(mul(unit, mul(p, q)), 1 / c**2)))
    root = sqrt_series(add(const(1), neg(mul(unit, w))))
    phase = scale(mul(w, inv(add(const(1), root))), -4 * c)
    correction = list(phase)
    correction[0] = sp.S.Zero
    exponential = exp_series(correction)
    inv_z = scale(mul(unit, inv(root)), 1 / (4 * c))
    acomp = polynomial(inv_z, relative_coefficients("A", N - 2))
    bcomp = polynomial(inv_z, relative_coefficients("B", N - 2))
    root_inv = inv(root)
    root_half_inv = inv(sqrt_series(root))
    root3 = mul(root_inv, root_half_inv)
    root5 = mul(mul(root_inv, root_inv), root_half_inv)
    dweight = scale(add(const(1), neg(mul(unit, add(p, q)))), 2)
    cc = 2 * c**2 - 1
    bracket = add(add(scale(mul(unit, p), -2 * cc),
                      scale(mul(unit, q), -cc)),
                  add(const(2 * cc + 1),
                      add(scale(mul(mul(unit, unit), mul(p, q)), 2),
                          add(scale(mul(unit, p), -1),
                              scale(mul(unit, q), -2)))))
    f_over = scale(mul(p, bracket), -4)
    kernel = mul(mul(root3, acomp), exponential)
    hregular = mul(mul(root5, bcomp), exponential)
    return {
        "kd": mul(kernel, dweight),
        "kf": mul(kernel, f_over),
        "hdd": mul(hregular, mul(dweight, dweight)),
        "hdf": mul(hregular, mul(dweight, f_over)),
    }


@lru_cache(maxsize=1)
def integrated_moments():
    # Keep the polynomial expressions.  Their Gaussian weight is evaluated
    # with Arb below; dropping it would produce a wildly invalid tail.
    return integrand_series()


def _poly_representation(expr):
    """Freeze sigma/tau monomials and c-polynomial coefficient data."""
    rows = []
    for (i, j), coefficient in sp.Poly(
            sp.expand(expr), sigma, tau).terms():
        numerator, denominator = sp.together(coefficient).as_numer_denom()
        np = [sp.Rational(x) for x in sp.Poly(numerator, c).all_coeffs()]
        dp = [sp.Rational(x) for x in sp.Poly(denominator, c).all_coeffs()]
        rows.append((i, j, np, dp))
    return tuple(rows)


@lru_cache(maxsize=1)
def frozen_terms():
    out = {}
    for name, values in integrated_moments().items():
        out[name] = tuple(_poly_representation(expr) for expr in values)
    return out


def eval_poly(expr, value):
    numerator, denominator = sp.together(expr).as_numer_denom()

    def horner(poly):
        coeffs = sp.Poly(poly, c).all_coeffs()
        out = arb(0)
        for coefficient in coeffs:
            out = out * value + arb(str(sp.Rational(coefficient)))
        return out

    return horner(numerator) / horner(denominator)


def eval_coefficients(coefficients, value):
    def horner(values):
        out = arb(0)
        for coefficient in values:
            out = out * value + arb(str(coefficient))
        return out
    return horner(coefficients[0]) / horner(coefficients[1])


def evaluate(t_lo, t_hi):
    ctx.prec = 140
    moment_terms = frozen_terms()
    def aq_sympy(value):
        value = sp.Rational(value)
        return arb(str(value.p)) / arb(str(value.q))

    c_box = hull((aq_sympy(t_lo) / 4).cos(),
                 (aq_sympy(t_hi) / 4).cos())
    def gaussian_moment(power):
        # The delta=0 phase is exp(-c*(sigma^2+tau^2)/2).
        a = c_box / 2
        exponent = arb(power + 1) / 2
        upper = a * 12**2
        return a**(-exponent) * upper.gamma_lower(exponent) / 2

    moments = {}
    for name, values in moment_terms.items():
        rows = []
        for terms in values:
            total = arb(0)
            for i, j, numerator, denominator in terms:
                total += eval_coefficients((numerator, denominator), c_box) \
                    * gaussian_moment(i) * gaussian_moment(j)
            rows.append(4 * total)
        moments[name] = arb_series(rows, N)
    bilinear = moments["kd"] * moments["hdf"] \
        - moments["kf"] * moments["hdd"]
    coeffs = bilinear.coeffs() + [arb(0)] * N
    quotient = arb_series(coeffs[1:N], N - 1)
    y = 4 * quotient / moments["kd"]**2
    return y.coeffs()[5], c_box


if __name__ == "__main__":
    coefficient, c_box = evaluate(sp.Rational(313, 100),
                                   sp.Rational(313, 100))
    print("R6 EXACT-MONOMIAL BOX PROBE")
    print("c", c_box.str(30))
    print("nominal_coefficient5", coefficient.str(30))
    print("DESIGN ONLY; companion and outer-tail charges open")
