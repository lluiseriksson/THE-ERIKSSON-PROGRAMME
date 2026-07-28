"""Fast exact-series derivation of the regularized S2 head through delta^5.

Unlike the independent ``sympy.series`` engine, this implementation stores
the seven delta coefficients separately throughout.  It reproduces the
registered ``r5`` before printing the new candidate coefficient.
"""

import sympy as sp

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_delta0_fifth_coefficient import target_y4


N = 7


def zero():
    return [sp.S.Zero]*N


def const(value):
    return [sp.sympify(value)]+[sp.S.Zero]*(N-1)


def add(a, b):
    return [x+y for x, y in zip(a, b)]


def neg(a):
    return [-x for x in a]


def scale(a, value):
    return [value*x for x in a]


def mul(a, b):
    return [sum((a[k]*b[n-k] for k in range(n+1)), sp.S.Zero)
            for n in range(N)]


def inv(a):
    out = zero(); out[0] = 1/a[0]
    for n in range(1, N):
        out[n] = -out[0]*sum((a[k]*out[n-k] for k in range(1, n+1)),
                             sp.S.Zero)
    return out


def sqrt_series(a):
    out = zero(); out[0] = sp.sqrt(a[0])
    for n in range(1, N):
        out[n] = (a[n]-sum((out[k]*out[n-k] for k in range(1, n)),
                           sp.S.Zero))/(2*out[0])
    return out


def exp_series(a):
    out = zero(); out[0] = sp.exp(a[0])
    for n in range(1, N):
        out[n] = sum((k*a[k]*out[n-k] for k in range(1, n+1)),
                     sp.S.Zero)/n
    return out


def polynomial(a, coefficients):
    out = const(0)
    for coefficient in reversed(coefficients):
        out = add(mul(out, a), const(sp.Rational(
            coefficient.numerator, coefficient.denominator)))
    return out


def derive_coefficients():
    c, sigma, tau = sp.symbols("c sigma tau", positive=True)
    s2, t2 = sigma**2, tau**2
    d = [sp.S.Zero, sp.S.One]+[sp.S.Zero]*(N-2)

    def sinc_square_scaled(x2):
        return [sp.Rational((-1)**n*2**(2*n+1), sp.factorial(2*n+2))
                *x2/4*(x2/4)**n for n in range(N)]

    p, q = sinc_square_scaled(s2), sinc_square_scaled(t2)
    w = add(add(p, q), neg(scale(mul(d, mul(p, q)), 1/c**2)))
    root = sqrt_series(add(const(1), neg(mul(d, w))))
    phase = scale(mul(w, inv(add(const(1), root))), -4*c)
    correction = list(phase); correction[0] = sp.S.Zero
    exponential = exp_series(correction)
    inv_z = scale(mul(d, inv(root)), 1/(4*c))
    acomp = polynomial(inv_z, relative_coefficients("A", N-1))
    bcomp = polynomial(inv_z, relative_coefficients("B", N-1))
    root_inv = inv(root)
    root_half_inv = inv(sqrt_series(root))
    root3 = mul(root_inv, root_half_inv)
    root5 = mul(mul(root_inv, root_inv), root_half_inv)
    dweight = scale(add(const(1), neg(mul(d, add(p, q)))), 2)
    cc = 2*c**2-1
    bracket = add(add(scale(mul(d, p), -2*cc),
                      scale(mul(d, q), -cc)),
                  add(const(2*cc+1),
                      add(scale(mul(mul(d, d), mul(p, q)), 2),
                          add(scale(mul(d, p), -1),
                              scale(mul(d, q), -2)))))
    f_over = scale(mul(p, bracket), -4)
    kernel = mul(mul(root3, acomp), exponential)
    hregular = mul(mul(root5, bcomp), exponential)
    integrands = {
        "KD": mul(kernel, dweight),
        "KF": mul(kernel, f_over),
        "HDD": mul(hregular, mul(dweight, dweight)),
        "HDF": mul(hregular, mul(dweight, f_over)),
    }

    def gaussian_expectation(expression):
        total = sp.S.Zero
        for (i, j), coefficient in sp.Poly(
                sp.expand(expression), sigma, tau).terms():
            if i % 2 or j % 2:
                continue
            mi = sp.factorial2(i-1)/c**(i//2) if i else 1
            mj = sp.factorial2(j-1)/c**(j//2) if j else 1
            total += coefficient*mi*mj
        return sp.cancel(total)

    moments = {name: [gaussian_expectation(value) for value in series]
               for name, series in integrands.items()}
    bilinear = add(mul(moments["KD"], moments["HDF"]),
                   neg(mul(moments["KF"], moments["HDD"])))
    if sp.simplify(bilinear[0]) != 0:
        raise AssertionError("exact B(0) cancellation failed")
    quotient = bilinear[1:]+[sp.S.Zero]
    y = scale(mul(quotient, mul(inv(moments["KD"]),
                                inv(moments["KD"]))), 1/(2*c))
    y = [sp.factor(value) for value in y[:6]]
    if sp.simplify(y[4]-target_y4(c)) != 0:
        raise AssertionError("registered r5 was not reproduced")
    return y


if __name__ == "__main__":
    result = derive_coefficients()
    print("FAST EXACT r5 reproduced =", result[4], flush=True)
    print("DESIGN candidate Y delta coefficient 5 =", result[5], flush=True)
    print("DESIGN ONLY: immutable target checker remains open", flush=True)
