"""Candidate fixed-beta pair Taylor probe; never a gate certificate."""

from fractions import Fraction
from math import comb, factorial

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_design as scaled


def hull_fraction(lo, hi):
    mid = (lo + hi) / 2; rad = (hi - lo) / 2
    return (scaled.bulk.aq(mid)
            + scaled.bulk.aq(rad) * arb("0 +/- 1"))


def sin_d(s, c, k):
    return (s, c, -s, -c)[k % 4]


def cos_d(s, c, k):
    return (c, -s, -c, s)[k % 4]


def run(beta, t_lo, t_hi, order=24, M=None):
    if M is None:
        M = int(beta) + 55
    J = {m: scaled.scaled_bessel_value(m, beta) for m in range(1, M + 2)}
    rho = {m: J[m+1] / J[m] for m in range(1, M + 1)}
    q = {m: (m-1)*(rho[m] + 2*arb(m)/scaled.bulk.aq(beta))**2
         + (m+1)*rho[m]**2 for m in range(1, M + 1)}
    T = scaled.bulk.aq((t_lo + t_hi) / 2)
    H = scaled.bulk.aq((t_hi - t_lo) / 2)
    poly = arb(0); abs_d = arb(0)
    for m in range(1, M + 1):
        sm = (arb(m)*T).sin(); cm = (arb(m)*T).cos()
        for n in range(m + 1, M + 1):
            sn = (arb(n)*T).sin(); cn = (arb(n)*T).cos()
            d = J[m]**4*J[n]**4*(arb(n)*q[m] - arb(m)*q[n])
            abs_d += 2*abs(d)
            for r in range(order + 1):
                kr = arb(0)
                for j in range(r + 1):
                    kr += arb(comb(r, j)) * (
                        arb(m)*arb(m)**j*cos_d(sm, cm, j)
                        *arb(n)**(r-j)*sin_d(sn, cn, r-j)
                        -arb(n)*arb(m)**j*sin_d(sm, cm, j)
                        *arb(n)**(r-j)*cos_d(sn, cn, r-j))
                poly += 2*d*kr*H**r/arb(factorial(r))
    rem = abs_d*(2*M)**(order+1)*abs(H)**(order+1)/arb(factorial(order+1))
    out = poly + (arb(0) + abs(rem)*arb("0 +/- 1"))
    return out


def main():
    ctx.prec = 500
    beta = Fraction(1629, 16)
    for t, width, order in ((Fraction(1311,500), Fraction(1,100000), 40),):
        out = run(beta, t, t+width, order=order)
        print("T", t, "WIDTH", width, "OUT", out.str(70),
              "NEGATIVE", bool(out < 0), flush=True)
    print("PAIR TAYLOR POINT PROBE ONLY; NO G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
