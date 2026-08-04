"""Arb (python-flint) port of certify_bridge_matrix.py - SECOND WITNESS.
Same algorithm, same pinned propositions and bounds: see the mpmath.iv twin.
Runs BOTH passes (M,prec) = (120,350) and (140,500) per cell and asserts
nesting. Cells: k = 1 (minimal counterexample, 2-step bridge midpoint),
k = 2, k = 4. (k = 3 is certified in certify_time3_negative_arb.py.)
"""
from flint import arb, ctx
from math import factorial


def ival(lo, hi):
    try:
        return lo.union(hi)
    except AttributeError:
        return (lo + hi) / 2 + ((hi - lo) / 2) * arb("0 +/- 1")


def besseli_arb(m, X):
    s = arb(0)
    j = 0
    while True:
        t = X ** (m + 2 * j) / (arb(factorial(j)) * arb(factorial(m + j)))
        s += t
        if (j + 1) * (m + j + 1) >= 200:
            if t < arb(10) ** (-160):
                r = arb(100) / (arb(j + 1) * arb(m + j + 1))
                s += ival(arb(0), t * r / (1 - r))
                return s
        j += 1


WITNESSES = {1: (9, 10), 2: (3, 4), 4: (3, 10)}


def certify_cell(k, M, prec):
    ctx.prec = prec
    X = arb(10)
    I = [besseli_arb(m, X) for m in range(M + 1)]
    A = arb(WITNESSES[k][0]) / arb(WITNESSES[k][1])
    T1 = arb(3)
    T2 = arb(61) / arb(20)
    PI = arb.pi()
    sa = [(arb(j) * A).sin() for j in range(2 * M + 1)]
    sv1 = [(arb(n) * T1).sin() for n in range(M + 1)]
    sv2 = [(arb(n) * T2).sin() for n in range(M + 1)]

    def assemble(sv):
        TN = arb(0)
        D = arb(0)
        for m in range(1, M + 1):
            cm = arb(m) * I[m] ** k
            row = arb(0)
            for n in range(1, M + 1):
                if m == n:
                    J = (PI - A) / 2 + sa[2 * m] / (arb(4) * arb(m))
                else:
                    sgn = 1 if m > n else -1
                    J = -(arb(sgn) * sa[abs(m - n)] / (arb(2) * arb(m - n))
                          - sa[m + n] / (arb(2) * arb(m + n)))
                row += arb(4) * I[n] * sv[n] * J
            TN += cm * row
            D += cm * arb(4) * I[m] * sv[m] * (PI / 2)
        return TN, D

    E100 = arb(100).exp()
    BM1 = X ** (M + 1) * E100 / arb(factorial(M + 1))
    tailI = BM1 / (1 - arb(10) / arb(M + 2))
    sumI = sum((I[n] for n in range(1, M + 1)), arb(0)) + tailI
    summk = sum((arb(m) * I[m] ** k for m in range(1, M + 1)), arb(0))
    tailmk = arb(2) * arb(M + 1) * BM1 ** k
    eps = arb(4) * PI * (tailmk * sumI + summk * tailI)
    ERR = ival(-eps, eps)

    TN1, D1 = assemble(sv1)
    TN2, D2 = assemble(sv2)
    TN1 += ERR; TN2 += ERR; D1 += ERR; D2 += ERR

    assert D1 > 0 and D2 > 0, "denominators not certified positive (k=%d)" % k
    diff = (TN2 * D1 - TN1 * D2) / (D1 * D2)
    assert diff < 0, "difference not certified negative (k=%d)" % k
    return diff


if __name__ == "__main__":
    for k in (1, 2, 4):
        d1 = certify_cell(k, M=120, prec=350)
        d2 = certify_cell(k, M=140, prec=500)
        lo1 = arb(d1.mid()) - arb(d1.rad()); hi1 = arb(d1.mid()) + arb(d1.rad())
        lo2 = arb(d2.mid()) - arb(d2.rad()); hi2 = arb(d2.mid()) + arb(d2.rad())
        assert lo1 <= lo2 and hi2 <= hi1, "NESTING FAILURE (k=%d)" % k
        print("k=%d CERTIFIED (Arb, nested):" % k, d2.str(30))
    print("ALL CROSSED CELLS CERTIFIED: k=1 (minimal), 2, 4 (+ k=3 sealed earlier)")
