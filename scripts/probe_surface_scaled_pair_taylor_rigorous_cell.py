"""Local pair-Taylor enclosure with non-proxy remainder accounting.

This is still a candidate transcript.  Unlike the earlier probe, the beta
remainder uses the (p+1)-st derivative bound already constructed by
``BetaTaylorBox.abs_sums`` and the omitted-mode contribution is explicitly
bounded for every retained beta/t Taylor coefficient.
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
    sm = (arb(m) * T).sin(); cm = (arb(m) * T).cos()
    sn = (arb(n) * T).sin(); cn = (arb(n) * T).cos()
    out = []
    for r in range(order + 1):
        kr = arb(0)
        for j in range(r + 1):
            kr += arb(comb(r, j)) * (
                arb(m) * arb(m) ** j * cos_d(sm, cm, j)
                * arb(n) ** (r - j) * sin_d(sn, cn, r - j)
                - arb(n) * arb(m) ** j * sin_d(sm, cm, j)
                * arb(n) ** (r - j) * cos_d(sn, cn, r - j))
        out.append(kr)
    return out


def build_abs_table(box, max_q, max_r, beta):
    """Positive all-mode sums of |m^r d_beta^q A_m| and B_m."""
    table = {}
    finite = {}
    for m in range(1, box.M + 1):
        finite[m] = scaled.scaled_coefficient_jets(m, beta, max_q)
    k = box.M + 1
    ak0 = scaled.scaled_coefficient_jets(k, beta, 0)[0][0]
    bk0 = scaled.scaled_coefficient_jets(k, beta, 0)[1][0]
    for q in range(max_q + 1):
        for r in range(max_r + 1):
            sa = arb(0); sb = arb(0)
            for m in range(1, box.M + 1):
                aj, bj = finite[m]
                sa += arb(m) ** r * aj[q].abs_upper()
                sb += arb(m) ** r * bj[q].abs_upper()
            sa += scaled.scaled_general_derivative_tail(
                ak0, k, box.r, box.beta_lo, q, r)
            sb += scaled.scaled_general_derivative_tail(
                bk0, k, box.r, box.beta_lo, q, r)
            table[q, r] = (sa, sb)
    return table


def beta_abs_mixed(table, q, r):
    """Positive bound for |d_beta^q d_t^r W| at the centre."""
    total = arb(0)
    for j in range(q + 1):
        aj1, bj = table[j, r + 1]
        aj, bj1 = table[j, r]
        ak1, bk = table[q - j, r + 1]
        ak, bk1 = table[q - j, r]
        total += arb(comb(q, j)) * (aj1 * bk + aj * bk1)
    return 2 * total


def omitted_abs_mixed(box, table, q, r):
    """Bound the part with at least one mode beyond the finite cutoff."""
    k = box.M + 1
    ta = scaled.scaled_general_derivative_tail(
        box.ac[k], k, box.r, box.beta_mid, q, r)
    tb = scaled.scaled_general_derivative_tail(
        box.bc[k], k, box.r, box.beta_mid, q, r)
    # The full positive sums use Arb absolute upper bounds.  This deliberately
    # overcounts the intersection of the two tails.
    sa, sb = table[q, r]
    return 2 * (ta * sb + sa * tb)


def beta_remainder_bound(table_hi, p, beta_rad):
    """Taylor remainder using the certified order-(p+1) absolute sums."""
    q = p + 1
    # Recompute endpoint absolute derivative sums with Arb upper bounds;
    # the design backend's signed sums are not used here.
    total = arb(0)
    for j in range(q + 1):
        Sa, Sb = table_hi[j, 0]
        Sma, Smb = table_hi[j, 1]
        Ta, Tb = table_hi[q - j, 0]
        Tma, Tmb = table_hi[q - j, 1]
        total += 2 * arb(comb(q, j)) * (Sma * Tb + Sa * Tmb)
    return beta_rad ** q * total / arb(factorial(q))


def run(beta_lo, beta_hi, t_lo, t_hi, beta_order=24, t_order=50,
        prec=350):
    ctx.prec = prec
    scaled.install_design_backend()
    box = scaled.bulk.BetaTaylorBox(
        beta_lo, beta_hi, prec=prec, order=beta_order, t_order=t_order)
    M = box.M
    Tmid = scaled.bulk.aq((t_lo + t_hi) / 2)
    Hb = scaled.bulk.aq((beta_hi - beta_lo) / 2)
    Ht = scaled.bulk.aq((t_hi - t_lo) / 2)
    table_mid = build_abs_table(box, beta_order + 1, t_order + 2,
                                box.beta_mid)
    table_hi = build_abs_table(box, beta_order + 1, 1, box.beta_hi)

    poly = arb(0)
    for m in range(1, M + 1):
        for n in range(m + 1, M + 1):
            Dj = []
            for q in range(beta_order + 1):
                d = arb(0)
                for j in range(q + 1):
                    d += arb(comb(q, j)) * (
                        box.aj[m][j] * box.bj[n][q - j]
                        - box.aj[n][j] * box.bj[m][q - j])
                Dj.append(d)
            Kj = kernel_jets(m, n, Tmid, t_order)
            for q, d in enumerate(Dj):
                for r, k in enumerate(Kj):
                    poly += (2 * d * k * Hb ** q * Ht ** r
                             / arb(factorial(q) * factorial(r)))

    # Bound only the omitted-mode part of every retained Taylor coefficient;
    # using the full absolute W bound here would erase the pair cancellation.
    omitted_poly = arb(0)
    for q in range(beta_order + 1):
        for r in range(t_order + 1):
            omitted_poly += (omitted_abs_mixed(box, table_mid, q, r)
                             * Hb ** q * Ht ** r
                             / arb(factorial(q) * factorial(r)))

    # The t remainder is summed over all beta Taylor coefficients, as in the
    # audited backend, and the beta remainder uses order p+1 (not a proxy).
    rt = t_order + 1
    t_rem = arb(0)
    for q in range(beta_order + 1):
        t_rem += (Hb ** q / arb(factorial(q)) * Ht ** rt
                  / arb(factorial(rt)) * beta_abs_mixed(table_mid, q, rt))
    b_rem = beta_remainder_bound(table_hi, beta_order, Hb)
    enclosure = poly + (omitted_poly + t_rem + b_rem) * arb("0 +/- 1")
    return poly, omitted_poly, t_rem, b_rem, enclosure


def main():
    lo = Fraction(1629, 16)
    hi = lo + Fraction(1, 16)
    vals = run(lo, hi, Fraction(1311, 500),
               Fraction(1311, 500) + Fraction(1, 1000))
    labels = ("POLY", "OMITTED_POLY", "T_REMAINDER", "BETA_REMAINDER",
              "ENCLOSURE")
    for label, value in zip(labels, vals):
        print(label, value.str(80))
    print("NEGATIVE", bool(vals[-1] < 0))
    print("PAIR TAYLOR RIGOROUS-ACCOUNTING CANDIDATE ONLY; NO G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
