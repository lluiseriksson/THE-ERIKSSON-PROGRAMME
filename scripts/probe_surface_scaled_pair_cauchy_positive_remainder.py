"""Positive complex-disc remainder estimate for the angular Cauchy probe.

This computes a conservative finite-mode majorant only.  The omitted-mode
tail and a formal complex-domain contract are intentionally not promoted.
"""

from fractions import Fraction
from math import comb, factorial

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_design as scaled


def main():
    ctx.prec = 220
    beta_mid = Fraction(1629, 16) + Fraction(1, 32)
    radius = Fraction(1, 10)
    re_min = beta_mid - radius
    x_abs = beta_mid + radius
    p = 50
    M = 220
    factor = (-(scaled.bulk.aq(re_min))).exp() \
        / (-(scaled.bulk.aq(x_abs))).exp()
    J = {m: factor*scaled.scaled_bessel_value(m, x_abs)
         for m in range(0, M + 3)}
    A = {}; B = {}; L = {}
    for m in range(1, M + 2):
        A[m] = J[m]**2*((m-1)*J[m-1]**2+(m+1)*J[m+1]**2)
        B[m] = arb(m)*J[m]**4
        L[m] = 8*(1+2*arb(m+1)/scaled.bulk.aq(re_min))
    major = arb(0)
    q = p + 1
    for m in range(1, M + 1):
        for n in range(m + 1, M + 1):
            kernel = arb(m+n)
            for j in range(q + 1):
                major += 2*kernel*arb(comb(q, j))* (
                    A[m]*L[m]**j*B[n]*L[n]**(q-j)
                    + A[n]*L[n]**j*B[m]*L[m]**(q-j))
    # Factorized all-mode majorant, including geometric tails beyond M.  The
    # ordered sum intentionally overcounts the pair domain but is a safe
    # diagnostic upper bound.
    ratio = scaled.bulk.coefficient_tail_ratio(scaled.bulk.aq(x_abs), M + 1)
    A0=[]; A1=[]; B0=[]; B1=[]
    tail_values = None
    for j in range(q + 1):
        a0=sum((A[m]*L[m]**j for m in range(1,M+1)),arb(0))
        a1=sum((arb(m)*A[m]*L[m]**j for m in range(1,M+1)),arb(0))
        b0=sum((B[m]*L[m]**j for m in range(1,M+1)),arb(0))
        b1=sum((arb(m)*B[m]*L[m]**j for m in range(1,M+1)),arb(0))
        ta0 = scaled.scaled_general_derivative_tail(A[M+1],M+1,ratio,re_min,j,0)
        ta1 = scaled.scaled_general_derivative_tail(A[M+1],M+1,ratio,re_min,j,1)
        tb0 = scaled.scaled_general_derivative_tail(B[M+1],M+1,ratio,re_min,j,0)
        tb1 = scaled.scaled_general_derivative_tail(B[M+1],M+1,ratio,re_min,j,1)
        a0 += ta0; a1 += ta1; b0 += tb0; b1 += tb1
        if j == 0: tail_values = (ta0,ta1,tb0,tb1)
        A0.append(a0); A1.append(a1); B0.append(b0); B1.append(b1)
    all_major=arb(0)
    for j in range(q+1):
        all_major += 2*arb(comb(q,j))*(
            A1[j]*B0[q-j]+A0[j]*B1[q-j]
            +B1[j]*A0[q-j]+B0[j]*A1[q-j])
    s = arb("0.1")*arb.pi()/64
    remainder = major*s**q/arb(factorial(q))
    print("BETA_MID", beta_mid, "RADIUS", radius,
          "ORDER", p, "MODES", M)
    print("POSITIVE_DERIVATIVE_MAJORANT", major.str(40))
    print("ALL_MODE_ORDERED_MAJORANT", all_major.str(40))
    ta0,ta1,tb0,tb1 = tail_values
    tail_w = 2*(ta1*B0[0] + ta0*B1[0] + tb1*A0[0] + tb0*A1[0])
    print("OMITTED_MODE_W_BOUND", tail_w.str(40))
    print("ANGULAR_DISPLACEMENT", s.str(30))
    print("ANGULAR_REMAINDER_ESTIMATE", remainder.str(40))
    print("ALL_MODE_REMAINDER_ESTIMATE", (all_major*s**q/arb(factorial(q))).str(40))
    print("FINITE-MODE DIAGNOSTIC ONLY; NO G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
