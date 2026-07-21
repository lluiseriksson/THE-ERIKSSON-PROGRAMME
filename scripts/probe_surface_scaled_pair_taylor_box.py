"""Candidate beta/t pair-Taylor enclosure for one scaled-bulk cell.

This is an engineering probe only.  It keeps the exact pair decomposition
before interval summation, adds conservative finite-mode Taylor remainders,
and deliberately carries no G2/G6 promotion path.
"""

from fractions import Fraction
from math import comb, factorial

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_design as scaled


def sin_d(s, c, k):
    return (s, c, -s, -c)[k % 4]


def cos_d(s, c, k):
    return (c, -s, -c, s)[k % 4]


def kernel_jets(m, n, T, order):
    sm = (arb(m)*T).sin(); cm = (arb(m)*T).cos()
    sn = (arb(n)*T).sin(); cn = (arb(n)*T).cos()
    out = []
    for r in range(order + 1):
        kr = arb(0)
        for j in range(r + 1):
            kr += arb(comb(r, j)) * (
                arb(m)*arb(m)**j*cos_d(sm, cm, j)
                *arb(n)**(r-j)*sin_d(sn, cn, r-j)
                -arb(n)*arb(m)**j*sin_d(sm, cm, j)
                *arb(n)**(r-j)*cos_d(sn, cn, r-j))
        out.append(kr)
    return out


def run(beta_lo, beta_hi, t_lo, t_hi, beta_order=8, t_order=30,
        prec=500):
    ctx.prec = prec
    scaled.install_design_backend()
    scaled.bulk.CWIN = Fraction(3, 2)
    box = scaled.bulk.BetaTaylorBox(beta_lo, beta_hi, prec=prec,
                                    order=beta_order, t_order=t_order)
    M = box.M
    Bmid = (beta_lo + beta_hi) / 2
    Tmid = scaled.bulk.aq((t_lo + t_hi) / 2)
    Hb = scaled.bulk.aq((beta_hi - beta_lo) / 2)
    Ht = scaled.bulk.aq((t_hi - t_lo) / 2)
    poly = arb(0)
    absD = [arb(0)]*(beta_order + 1)
    for m in range(1, M + 1):
        for n in range(m + 1, M + 1):
            Dj = []
            for q in range(beta_order + 1):
                d = arb(0); ad = arb(0)
                for j in range(q + 1):
                    x = box.aj[m][j]*box.bj[n][q-j]
                    y = box.aj[n][j]*box.bj[m][q-j]
                    d += arb(comb(q, j))*(x-y)
                    ad += arb(comb(q, j))*(abs(x)+abs(y))
                Dj.append(d); absD[q] += 2*ad
            Kj = kernel_jets(m, n, Tmid, t_order)
            for q, d in enumerate(Dj):
                hbq = Hb**q/arb(factorial(q))
                for r, k in enumerate(Kj):
                    poly += 2*d*k*hbq*Ht**r/arb(factorial(r))
    # Conservative mixed Taylor remainder for the finite pair sum.  The
    # bound |K_mn^(r)| <= (m+n)^(r+1) is intentionally simple.
    t_abs = arb(0)
    for m in range(1, M + 1):
        for n in range(m + 1, M + 1):
            t_abs += (arb(m+n)**(t_order+1))
    rem_t = absD[0]*Ht**(t_order+1)*t_abs/arb(factorial(t_order+1))
    rem_b = absD[beta_order]*Hb**(beta_order+1)/arb(factorial(beta_order+1))
    # Bound pair terms with at least one omitted mode using the positive
    # coefficient tails supplied by the scaled backend.  The Taylor
    # remainder itself remains candidate-only because the next beta jet is
    # not reconstructed in this probe.
    k = M + 1
    at0 = scaled.scaled_general_derivative_tail(
        box.ac[k], k, box.r, box.beta_mid, 0, 0)
    at1 = scaled.scaled_general_derivative_tail(
        box.ac[k], k, box.r, box.beta_mid, 0, 1)
    bt0 = scaled.scaled_general_derivative_tail(
        box.bc[k], k, box.r, box.beta_mid, 0, 0)
    bt1 = scaled.scaled_general_derivative_tail(
        box.bc[k], k, box.r, box.beta_mid, 0, 1)
    A0, B0 = box.abs_center[0][0]
    A1, B1 = box.abs_center[0][1]
    tail_err = 2*(at1*B0 + at0*B1 + bt1*A0 + bt0*A1)
    return poly, rem_t, rem_b + tail_err


def main():
    lo = Fraction(1629, 16); hi = lo + Fraction(1, 16)
    poly, rem_t, rem_b = run(lo, hi, Fraction(1311,500), Fraction(1311,500)+Fraction(1,1000), beta_order=24, t_order=50)
    out = poly + (rem_t + rem_b)*arb("0 +/- 1")
    print("CELL", lo, hi, "POLY", poly.str(60),
          "REM_T", rem_t.str(20), "REM_B", rem_b.str(20),
          "OUT", out.str(80), "NEGATIVE", bool(out < 0))
    print("PAIR BETA/T TAYLOR PROBE ONLY; NO G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
