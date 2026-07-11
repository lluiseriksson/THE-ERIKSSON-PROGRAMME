"""EXACT adjudication of MD c6 (eps^12) and c7 (eps^14) at the mirror
zone floor p = 5801/10000, Fraction dict engine, NORD = 16 (complete
for eps^{<=14}); internal series depths >= committed (cos 8 terms,
binom order 9, exp 8 terms).  Independent of both prior engines."""
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps = 40

NORD = 16
P = Fr(5801, 10000)

def pmul(A, B):
    C = {}
    for (i1, j1, k1), c1 in A.items():
        for (i2, j2, k2), c2 in B.items():
            k = k1 + k2
            if k >= NORD:
                continue
            key = (i1 + i2, j1 + j2, k)
            C[key] = C.get(key, 0) + c1*c2
    return {k: c for k, c in C.items() if c != 0}

def padd(*polys):
    C = {}
    for A in polys:
        for k, c in A.items():
            C[k] = C.get(k, 0) + c
    return {k: c for k, c in C.items() if c != 0}

def pscale(A, s):
    return {k: s*c for k, c in A.items()}

def cospoly(vi):
    out = {}
    f = 1
    for m in range(0, 8):          # to eps^14, same as committed
        key = (2*m, 0, 2*m) if vi == 0 else (0, 2*m, 2*m)
        out[key] = Fr((-1)**m, f)
        f *= (2*m + 1)*(2*m + 2)
    return out

one = {(0, 0, 0): Fr(1)}
x = cospoly(0); y = cospoly(1)
# mirror chart
C_ = 1 - 2*P*P
D = pscale(padd(x, y), Fr(-1))
Pp = pscale(padd(one, pscale(x, Fr(-1))), Fr(1, 2))
Qq = pscale(padd(one, pscale(y, Fr(-1))), Fr(1, 2))
w = padd(Pp, Qq, pscale(pmul(Pp, Qq), -1/(P*P)))

def binom_series(A, alpha_num, alpha_den, mmax):
    # alpha = alpha_num/alpha_den exact
    alpha = Fr(alpha_num, alpha_den)
    out = dict(one)
    term = dict(one)
    coef = Fr(1)
    for m in range(1, mmax + 1):
        coef *= (alpha - m + 1)/m
        term = pmul(term, A)
        out = padd(out, pscale(term, coef*Fr((-1)**m)))
    return out

sqrt1mw = binom_series(w, 1, 2, 9)
inv_sqrt = binom_series(w, -1, 2, 9)
pow34 = binom_series(w, -3, 4, 9)

shifted = {}
for (i, j, k), c in padd(sqrt1mw, pscale(one, Fr(-1))).items():
    assert k - 2 >= 0
    shifted[(i, j, k - 2)] = 4*P*c
rho2 = {(2, 0, 0): P/2, (0, 2, 0): P/2}
expo = padd(shifted, rho2)
assert all(k[2] != 0 for k in expo), "expo eps^0 survives"

wcorr = dict(one)
term = dict(one)
for n in range(1, 9):              # 8 exp terms (>= committed 7)
    term = pscale(pmul(term, expo), Fr(1, n))
    wcorr = padd(wcorr, term)

invz = {(i, j, k + 2): c/(4*P)
        for (i, j, k), c in inv_sqrt.items() if k + 2 < NORD}
KER = pmul(pmul(pow34, wcorr), padd(one, pscale(invz, Fr(-3, 8))))
integ = pmul(D, KER)

# plane moment: for even i,j: int |s|^i e^{-p s^2/2} = sqrt(2pi/p) (i-1)!!/p^{i/2}
# c_j = CONV * fac * [coeff of eps^{2j}], CONV = 2/(sqrt(2pi)(4p)^{3/2})
# rational split: gauss(i)gauss(j) = (2pi/p) f2(i)f2(j)/p^{(i+j)/2}
def f2(m):
    r = Fr(1)
    while m > 1:
        r *= m - 1
        m -= 2
    return r

S = {}
for (i, j, k), c in integ.items():
    if i % 2 or j % 2:
        continue
    S[k] = S.get(k, Fr(0)) + c*f2(i)*f2(j)/P**((i + j)//2)

pmp = mp.mpf(5801)/10000
pref = 2*mp.sqrt(2*mp.pi)/((4*pmp)**mp.mpf('1.5')*pmp)   # CONV*(2pi/p)/sqrt(2pi)... see split
# check split: CONV*(2pi/p) = [2/(sqrt(2pi)(4p)^1.5)]*(2pi/p) = 2 sqrt(2pi)/((4p)^1.5 p)
for j in range(0, 8):
    k = 2*j
    Sv = S.get(k, Fr(0))
    c = pref*mp.mpf(Sv.numerator)/mp.mpf(Sv.denominator)
    print("c%d (eps^%d) exact-engine = %s" % (j, k, mp.nstr(c, 10)))
print()
print("committed NORD=14 script:  c6 = -14769.2")
print("prior-audit stage2 (float NORD=16): c6 = -14791 (transcript)")
