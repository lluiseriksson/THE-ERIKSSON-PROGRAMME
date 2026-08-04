"""Arb (python-flint) port of certify_time3_negative.py — SECOND WITNESS.

Same algorithm, same pinned statement, same algebraic bounds: see the
docstring of certify_time3_negative.py (the mpmath.iv twin) for the full
proposition, method, and truncation bounds. Two independent interval
implementations agreeing is stronger than one.

Trust base here: Arb ball arithmetic via python-flint.
"""
from flint import arb, ctx
from math import factorial


def ival(lo, hi):
    """Ball containing [lo, hi]."""
    try:
        return lo.union(hi)
    except AttributeError:
        return (lo + hi) / 2 + ((hi - lo) / 2) * arb("0 +/- 1")


def besseli_arb(m, X):
    """Enclosure of I_m(20): positive-term series + geometric tail."""
    s = arb(0)
    j = 0
    while True:
        t = X ** (m + 2 * j) / (arb(factorial(j)) * arb(factorial(m + j)))
        s += t
        if (j + 1) * (m + j + 1) >= 200:  # exact integer test: ratio <= 1/2
            if t < arb(10) ** (-160):  # heuristic stop only
                r = arb(100) / (arb(j + 1) * arb(m + j + 1))
                s += ival(arb(0), t * r / (1 - r))
                return s
        j += 1


def certify(M, prec):
    ctx.prec = prec
    X = arb(10)  # beta/2, exact
    I = [besseli_arb(m, X) for m in range(M + 1)]
    A = arb(4802) / arb(10000)
    T1 = arb(29621) / arb(10000)
    T2 = arb(30070) / arb(10000)
    PI = arb.pi()
    sa = [(arb(k) * A).sin() for k in range(2 * M + 1)]
    sv1 = [(arb(n) * T1).sin() for n in range(M + 1)]
    sv2 = [(arb(n) * T2).sin() for n in range(M + 1)]

    def assemble(sv):
        TN = arb(0)
        D = arb(0)
        for m in range(1, M + 1):
            cm = arb(m) * I[m] ** 3
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

    # truncation error, computed in balls (bounds: see mpmath twin docstring)
    E100 = arb(100).exp()
    BM1 = X ** (M + 1) * E100 / arb(factorial(M + 1))
    tailI = BM1 / (1 - arb(10) / arb(M + 2))
    sumI = sum((I[n] for n in range(1, M + 1)), arb(0)) + tailI
    summ3 = sum((arb(m) * I[m] ** 3 for m in range(1, M + 1)), arb(0))
    tailm3 = arb(2) * arb(M + 1) * BM1 ** 3
    eps = arb(4) * PI * (tailm3 * sumI + summ3 * tailI)
    ERR = ival(-eps, eps)

    TN1, D1 = assemble(sv1)
    TN2, D2 = assemble(sv2)
    TN1 += ERR; TN2 += ERR; D1 += ERR; D2 += ERR

    assert D1 > 0 and D2 > 0, "denominators not certified positive"
    R = TN2 * D1 - TN1 * D2
    diff = R / (D1 * D2)
    assert diff < 0, "difference not certified negative"
    return diff


if __name__ == "__main__":
    d1 = certify(M=120, prec=350)
    print("pass 1 (M=120, prec=350):", d1.str(40))
    d2 = certify(M=140, prec=500)
    print("pass 2 (M=140, prec=500):", d2.str(60))
    lo1 = arb(d1.mid()) - arb(d1.rad()); hi1 = arb(d1.mid()) + arb(d1.rad())
    lo2 = arb(d2.mid()) - arb(d2.rad()); hi2 = arb(d2.mid()) + arb(d2.rad())
    assert lo1 <= lo2 and hi2 <= hi1, "NESTING FAILURE"
    print("NESTING OK; CERTIFIED (Arb): T(t2,a) - T(t1,a) < 0")
