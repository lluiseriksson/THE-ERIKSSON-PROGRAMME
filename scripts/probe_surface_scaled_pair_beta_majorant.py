"""Measure the positive beta-derivative majorant for pair regrouping.

Diagnostic only: it deliberately measures how much cancellation is lost when
the next beta Taylor remainder is bounded by positive Bessel monomials.
"""

from fractions import Fraction
from math import comb, factorial

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_design as scaled


def main():
    ctx.prec = 220
    lo = Fraction(1629, 16); hi = lo + Fraction(1, 16)
    p = 24
    M = int(hi) + 55
    # Positive values at beta_hi and the derivative-growth majorant used by
    # the audited scaled tail contract.
    aa = {}; bb = {}; L = {}
    for m in range(1, M + 1):
        aj, bj = scaled.scaled_coefficient_jets(m, hi, 0)
        aa[m], bb[m] = aj[0], bj[0]
        L[m] = 8*(1 + 2*arb(m+1)/scaled.bulk.aq(lo))
    absd = arb(0)
    for m in range(1, M + 1):
        for n in range(m + 1, M + 1):
            for j in range(p + 2):
                absd += 2*arb(comb(p+1, j))* (
                    aa[m]*L[m]**j*bb[n]*L[n]**(p+1-j)
                    + aa[n]*L[n]**j*bb[m]*L[m]**(p+1-j))
    H = scaled.bulk.aq((hi-lo)/2)
    remainder = absd*H**(p+1)/arb(factorial(p+1))
    print("BETA", lo, hi, "ORDER", p,
          "ABS_POSITIVE_D_NEXT", absd.str(30),
          "REMAINDER", remainder.str(30))
    print("PAIR BETA MAJORANT DIAGNOSTIC ONLY; NO G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
