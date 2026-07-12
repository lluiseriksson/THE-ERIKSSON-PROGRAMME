"""Exact first two delta coefficients of the regularized S2 carrier.

The calculation uses polynomial algebra and exact Gaussian moments only.
It proves that the first nonzero bilinear coefficient gives Y(0,t)=T(c)
and that the next coefficient is r2(c).  It does not bound the Taylor tail.
"""

import sympy as sp


d, c, sigma, tau = sp.symbols("delta c sigma tau", positive=True)
s2, t2 = sigma**2, tau**2


def trunc2(expression):
    return sp.series(expression, d, 0, 3).removeO().expand()


# Entire sinc-squared geometry through first order.
P = (s2/sp.Integer(4)-d*s2**2/sp.Integer(48)
     +d**2*s2**3/sp.Integer(1440))
Q = (t2/sp.Integer(4)-d*t2**2/sp.Integer(48)
     +d**2*t2**3/sp.Integer(1440))
w_over = trunc2(P+Q-d*P*Q/c**2)
w = d*w_over
root = trunc2(sp.sqrt(1-w))
phase = trunc2(-4*c*w_over/(1+root))
phase0 = sp.simplify(phase.subs(d, 0))
phase1 = sp.simplify(phase.coeff(d, 1))
assert sp.simplify(phase0+c*(s2+t2)/2) == 0
exp_correction = trunc2(sp.exp(phase-phase0))
inv_z = trunc2(d/(4*c*root))

# Fifth-order companions are needed only through their first coefficient here.
a_relative = trunc2(1-sp.Rational(3, 8)*inv_z
                    -sp.Rational(15, 128)*inv_z**2)
b_relative = trunc2(1-sp.Rational(15, 8)*inv_z
                    +sp.Rational(105, 128)*inv_z**2)
d_weight = trunc2(2*(1-d*(P+Q)))
cc = 2*c**2-1
f_over = trunc2(-4*P*(
    -2*cc*P*d-cc*Q*d+2*cc+2*P*Q*d**2-P*d-2*Q*d+1
))

k_regular = trunc2(root**sp.Rational(-3, 2)*a_relative*exp_correction)
h_regular = trunc2(root**sp.Rational(-5, 2)*b_relative*exp_correction)

integrands = {
    "KD": trunc2(k_regular*d_weight),
    "KF1": trunc2(k_regular*f_over),
    "HDD2": trunc2(h_regular*d_weight**2),
    "HDF3": trunc2(h_regular*d_weight*f_over),
}


def gaussian_expectation(poly):
    """Expectation under independent N(0,1/c) coordinates."""
    total = 0
    for term in sp.Poly(sp.expand(poly), sigma, tau).terms():
        (i, j), coefficient = term
        if i % 2 or j % 2:
            continue
        mi = sp.factorial2(i-1)/c**(i//2) if i else 1
        mj = sp.factorial2(j-1)/c**(j//2) if j else 1
        total += coefficient*mi*mj
    return sp.factor(total)


moments = {
    name: [gaussian_expectation(value.coeff(d, order))
           for order in (0, 1, 2)]
    for name, value in integrands.items()
}

kd0, kd1, kd2 = moments["KD"]
kf0, kf1, kf2 = moments["KF1"]
hd0, hd1, hd2 = moments["HDD2"]
hf0, hf1, hf2 = moments["HDF3"]

leading_bilinear = sp.factor(kd0*hf0-kf0*hd0)
first_bilinear = sp.factor(kd0*hf1+kd1*hf0-kf0*hd1-kf1*hd0)
second_bilinear = sp.factor(
    kd0*hf2+kd1*hf1+kd2*hf0-kf0*hd2-kf1*hd1-kf2*hd0)

# h_constant/k_constant = 1/(8c); Y=4 B/(delta KD^2).
y0 = sp.factor(first_bilinear/(2*c*kd0**2))
target = (4*c**2-1)/(8*c**3)
y1 = sp.factor((second_bilinear/kd0**2
                -2*first_bilinear*kd1/kd0**3)/(2*c))
r2_target = (-8*c**4+15*c**2-4)/(32*c**6)

assert leading_bilinear == 0
assert sp.simplify(y0-target) == 0
assert sp.simplify(y1-r2_target) == 0


def check():
    print("leading bilinear coefficient =", leading_bilinear)
    print("first bilinear coefficient =", first_bilinear)
    print("second bilinear coefficient =", second_bilinear)
    print("Y(0,t) =", y0)
    print("TARGET MATCH: T(c)=(4c^2-1)/(8c^3)")
    print("Y_delta(0,t) =", y1)
    print("TARGET MATCH: r2(c)=(-8c^4+15c^2-4)/(32c^6)")


if __name__ == "__main__":
    check()
