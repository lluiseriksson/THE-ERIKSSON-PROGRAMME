"""CERTIFIED NEGATIVES - the weight x kernel matrix, remaining crossed cells.

PINNED FAMILY OF PROPOSITIONS (normalizations as in certify_time3_negative.py:
q1, s1, Q with eigenvalues I_m(beta); beta = 20 throughout).
For k in {1, 2, 4}, consider the marginal ONE q1-step from the moving
endpoint t, with entry weight Q^{k-1} s1:
    rho_t(u) prop. (Q^{k-1} s1)(u) * q1(u,t),
    (Q^{k-1} s1)(u) = sum_{m>=1} m I_m(beta)^k sin(mu).
CLAIMS (one certified witness each, t1 = 3, t2 = 61/20 shared):
  k=1 (midpoint of the 2-STEP bridge, the MINIMAL counterexample):
      a = 9/10:   T(t2,a) < T(t1,a)   [margin ~ -1.34e-2]
  k=2 (time-2 of the 3-step bridge):
      a = 3/4:    T(t2,a) < T(t1,a)   [margin ~ -1.80e-6]
  k=4 (time-4 of the 5-step bridge):
      a = 3/10:   T(t2,a) < T(t1,a)   [margin ~ -4.75e-13]
(k=3, time-3 of the 4-step bridge, is certified in
certify_time3_negative.py.) Together: the marginal one smoothing step from
the moving endpoint is NOT stochastically monotone against ANY weight of the
natural family Q^{k-1}s1 at beta = 20 - the st-fragility lives on the
endpoint side, and no amount of smoothing on the weight side repairs it.

METHOD, TRUST BASE, BESSEL ENCLOSURES, TRUNCATION BOUNDS: identical to
certify_time3_negative.py (exact termwise tails via J(m,n,a); mpmath.iv
outward rounding; positive-term series + geometric tails; the m I_m^k tail
uses sum_{m>M} m B_m^k <= 2 (M+1) B_{M+1}^k, valid for k >= 1, M >= 120,
since (m+1)B_{m+1}^k/(m B_m^k) = (10/(m+1))^k (m+1)/m <= 20/121 < 1/2).
Nested enclosures prevent silent numerical or truncation degradation;
statement auditing and the independent Arb implementation
(certify_bridge_matrix_arb.py) guard against common-mode errors.
"""
from mpmath import iv
from math import factorial


def besseli_iv(m, X):
    s = iv.mpf(0)
    j = 0
    while True:
        t = X ** (m + 2 * j) / (iv.mpf(factorial(j)) * iv.mpf(factorial(m + j)))
        s += t
        if (j + 1) * (m + j + 1) >= 200:
            if float(t.b) < 1e-120 * max(float(s.a), 1e-300):
                r = iv.mpf(100) / (iv.mpf(j + 1) * iv.mpf(m + j + 1))
                s += iv.mpf([0, 1]) * (t * r / (1 - r))
                return s
        j += 1


WITNESSES = {1: (9, 10), 2: (3, 4), 4: (3, 10)}  # a as exact fractions
T1_FRAC = (3, 1)
T2_FRAC = (61, 20)


def certify_cell(k, M, prec):
    iv.prec = prec
    X = iv.mpf(10)
    I = [besseli_iv(m, X) for m in range(M + 1)]
    A = iv.mpf(WITNESSES[k][0]) / iv.mpf(WITNESSES[k][1])
    T1 = iv.mpf(T1_FRAC[0]) / iv.mpf(T1_FRAC[1])
    T2 = iv.mpf(T2_FRAC[0]) / iv.mpf(T2_FRAC[1])
    PI = iv.pi
    sa = [iv.sin(iv.mpf(j) * A) for j in range(2 * M + 1)]
    sv1 = [iv.sin(iv.mpf(n) * T1) for n in range(M + 1)]
    sv2 = [iv.sin(iv.mpf(n) * T2) for n in range(M + 1)]

    def assemble(sv):
        TN = iv.mpf(0)
        D = iv.mpf(0)
        for m in range(1, M + 1):
            cm = iv.mpf(m) * I[m] ** k
            row = iv.mpf(0)
            for n in range(1, M + 1):
                if m == n:
                    J = (PI - A) / 2 + sa[2 * m] / (iv.mpf(4) * iv.mpf(m))
                else:
                    sgn = 1 if m > n else -1
                    J = -(iv.mpf(sgn) * sa[abs(m - n)] / (iv.mpf(2) * iv.mpf(m - n))
                          - sa[m + n] / (iv.mpf(2) * iv.mpf(m + n)))
                row += iv.mpf(4) * I[n] * sv[n] * J
            TN += cm * row
            D += cm * iv.mpf(4) * I[m] * sv[m] * (PI / 2)
        return TN, D

    E100 = iv.exp(iv.mpf(100))
    BM1 = X ** (M + 1) * E100 / iv.mpf(factorial(M + 1))
    tailI = BM1 / (1 - iv.mpf(10) / iv.mpf(M + 2))
    sumI = sum(I[n] for n in range(1, M + 1)) + tailI
    summk = sum(iv.mpf(m) * I[m] ** k for m in range(1, M + 1))
    tailmk = iv.mpf(2) * iv.mpf(M + 1) * BM1 ** k
    eps = iv.mpf(4) * PI * (tailmk * sumI + summk * tailI)
    ERR = iv.mpf([-1, 1]) * eps

    TN1, D1 = assemble(sv1)
    TN2, D2 = assemble(sv2)
    TN1 += ERR; TN2 += ERR; D1 += ERR; D2 += ERR

    assert D1 > 0 and D2 > 0, "denominators not certified positive (k=%d)" % k
    diff = (TN2 * D1 - TN1 * D2) / (D1 * D2)
    assert diff < 0, "difference not certified negative (k=%d)" % k
    return diff


if __name__ == "__main__":
    import sys
    ks = [int(x) for x in sys.argv[1:]] or [1, 2, 4]
    for k in ks:
        d1 = certify_cell(k, M=120, prec=350)
        d2 = certify_cell(k, M=140, prec=500)
        # nesting: refined enclosure must lie inside the coarse one
        assert d1.a <= d2.a and d2.b <= d1.b, "NESTING FAILURE (k=%d)" % k
        print("k=%d CERTIFIED negative (both passes, NESTED):" % k,
              str(d2)[:60], "...]")
