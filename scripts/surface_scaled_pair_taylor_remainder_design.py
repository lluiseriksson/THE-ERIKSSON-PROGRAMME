"""Design-only absolute Taylor-remainder majorants for the pair lane.

This module deliberately does not promote a gate.  It tests whether a
coefficientwise Arb majorant for the omitted beta/lambda terms is small enough
to sit below the observed negative pair-sum margin.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, factorial

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_design as scaled
import certify_bulk_beta_taylor_arb as bulk
from surface_scaled_pair_taylor_design import trig_bivariate


def aq(x):
    if isinstance(x, Fraction):
        return arb(x.numerator) / x.denominator
    return arb(x)


def interval_bessel_jet(n: int, beta_box: arb, order: int, vals=None):
    if vals is None:
        vals = {k: (-beta_box).exp() * beta_box.bessel_i(k)
                for k in range(max(0, abs(n)-order), abs(n)+order+1)}
    i = []
    for q in range(order + 1):
        derivative = sum((arb(comb(q, j))*vals[abs(n-q+2*j)]
                          for j in range(q+1)), arb(0)) / arb(2)**q
        i.append(derivative / arb(factorial(q)))
    return [sum((i[j]*arb((-1)**(q-j))/arb(factorial(q-j))
                 for j in range(q+1)), arb(0)) for q in range(order+1)]


def interval_coefficient_jets(m: int, beta_box: arb, order: int, vals=None):
    jm = interval_bessel_jet(m, beta_box, order, vals)
    jl = interval_bessel_jet(m-1, beta_box, order, vals)
    jr = interval_bessel_jet(m+1, beta_box, order, vals)
    jm2 = bulk.jet_mul(jm, jm, order)
    jl2 = bulk.jet_mul(jl, jl, order)
    jr2 = bulk.jet_mul(jr, jr, order)
    q = [(m-1)*jl2[j] + (m+1)*jr2[j] for j in range(order+1)]
    aj = bulk.jet_mul(jm2, q, order)
    bj = bulk.jet_mul(jm2, jm2, order)
    return ([aj[j]*factorial(j) for j in range(order+1)],
            [arb(m)*bj[j]*factorial(j) for j in range(order+1)])


def abs_upper(x):
    return x.abs_upper()


def remainder_majorant(beta_lo, beta_hi, lambda_mid, lambda_radius,
                       *, modes=120, beta_order=30, lambda_order=28,
                       precision=600):
    """Return (lambda remainder, beta remainder) for the retained modes."""
    ctx.prec = precision
    beta_box = aq((beta_lo + beta_hi)/2) + aq((beta_hi-beta_lo)/2)*arb("0 +/- 1")
    br = aq((beta_hi-beta_lo)/2)
    lm = aq(lambda_mid)
    lr = aq(lambda_radius)
    # beta jets enclose derivatives throughout the beta box.
    jet_order = max(beta_order+1, lambda_order+1)
    bessel_values = {k: (-beta_box).exp() * beta_box.bessel_i(k)
                     for k in range(modes + jet_order + 2)}
    coeff_der = [interval_coefficient_jets(m, beta_box, jet_order,
                                           bessel_values)
             for m in range(1, modes+1)]
    coeff = [([v/arb(factorial(j)) for j, v in enumerate(a)],
              [v/arb(factorial(j)) for j, v in enumerate(b)])
             for a, b in coeff_der]
    lam_abs = arb(0)
    beta_abs = arb(0)
    # phase beta jets for each pair and lambda Taylor coefficient.
    inv_beta = [1/beta_box] + [arb(0)]*(beta_order+1)
    inv_beta[1] = -1/(beta_box*beta_box)
    # Construct exact formal inverse jet around the interval base.
    inv_beta = [1/beta_box] + [arb(0)]*(beta_order+1)
    for q in range(1, beta_order+2):
        inv_beta[q] = (-1)**q / beta_box**(q+1)
    x = [lm*inv_beta[i] for i in range(beta_order+2)]
    trig = {k: trig_bivariate(k, x, inv_beta, lambda_order)
            for k in range(1, 2*modes+1)}
    # Cache each pair minor's factorial-divided beta coefficients.  Keeping
    # the minor paired in the beta remainder is essential: aggregating by
    # frequency first loses the cancellation and gives a useless majorant.
    pair_data = []
    for m in range(1, modes+1):
        am, bm = coeff[m-1]
        for n in range(m+1, modes+1):
            an, bn = coeff[n-1]
            p, q = n-m, n+m
            minor = [sum((am[u]*bn[j-u] - an[u]*bm[j-u]
                          for u in range(j+1)), arb(0))
                     for j in range(jet_order + 1)]
            minor_bound = abs_upper(am[0]*bn[0]) + abs_upper(an[0]*bm[0])
            pair_data.append((m, n, p, q, minor, minor_bound))

    # Lambda remainder is a positive pairwise majorant; it does not use the
    # signed frequency cancellation.
    for m, n, p, q, _, minor_bound in pair_data:
        lam_abs += minor_bound * (p*(aq(q)/beta_box)**(lambda_order+1)
                                  + q*(aq(p)/beta_box)**(lambda_order+1)) \
                    * lr**(lambda_order+1) / factorial(lambda_order+1)

    # Keep the pair loop below for the beta remainder, preserving its exact
    # cancellation.  The phase rows were precomputed once per frequency.
    z = beta_order + 1
    for m, n, p, q, minor, _ in pair_data:
        for r in range(lambda_order + 1):
            phase = [(m-n)*trig[q][0][r][j]
                     + q*trig[p][0][r][j]
                     for j in range(z+1)]
            conv = sum((minor[j] * phase[z-j] for j in range(z+1)), arb(0))
            beta_abs += abs_upper(conv) * br**z * lr**r
    return lam_abs, beta_abs


if __name__ == "__main__":
    # Kept as a smoke experiment; no production transcript is emitted.
    lo, hi = Fraction(1629, 16), Fraction(3259, 32)
    lam, bet = remainder_majorant(lo, hi, Fraction(299, 100),
                                  Fraction(1, 200), modes=20,
                                  beta_order=8, lambda_order=8, precision=180)
    print("DESIGN ONLY", lam.str(20), bet.str(20))
