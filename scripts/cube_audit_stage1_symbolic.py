"""INTERNAL CUBE AUDIT - stage 1: independent symbolic rebuild of the
seven judged moments' lead+next coefficients at NORD=8 (different
truncation depth; clean-room dict-based engine, NOT the committed
build()).  Compares symbolically against the v63/v67 closed forms.

Engine representation: polynomial = dict {(i,j,k): sympy expr in p}
for monomials sigma^i tau^j eps^k.  Truncation keeps k < NORD.
"""
import hashlib
import sys
from itertools import product as iproduct

import sympy as sp

p = sp.Symbol('p', positive=True)

NORD = 8

print("=== CUBE AUDIT stage 1: symbolic lead/next, own engine, NORD=%d ==="
      % NORD)
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("sympy %s python %s" % (sp.__version__, sys.version.split()[0]),
      flush=True)


def pmul(A, B, nord=NORD):
    C = {}
    for (i1, j1, k1), c1 in A.items():
        for (i2, j2, k2), c2 in B.items():
            if k1 + k2 >= nord:
                continue
            key = (i1 + i2, j1 + j2, k1 + k2)
            C[key] = C.get(key, 0) + c1 * c2
    return {k: sp.expand(v) for k, v in C.items()
            if sp.expand(v) != 0}


def padd(*polys):
    C = {}
    for A in polys:
        for k, c in A.items():
            C[k] = C.get(k, 0) + c
    return {k: sp.expand(v) for k, v in C.items() if sp.expand(v) != 0}


def pscale(A, s):
    return {k: sp.expand(s * c) for k, c in A.items()}


def cospoly(var_index):
    """cos(v*eps) with v = sigma (var_index=0) or tau (1)."""
    out = {}
    m = 0
    while 2 * m < NORD:
        key = (2 * m, 0, 2 * m) if var_index == 0 else (0, 2 * m, 2 * m)
        out[key] = sp.Rational((-1) ** m, sp.factorial(2 * m))
        m += 1
    return out


def binom_series(A, alpha, mmax):
    """(1 - A)^alpha = sum_m binom(alpha,m) (-A)^m, A = O(eps^2)."""
    out = {(0, 0, 0): sp.Integer(1)}
    term = {(0, 0, 0): sp.Integer(1)}
    for m in range(1, mmax + 1):
        coef = sp.binomial(alpha, m) * (-1) ** m
        term = pmul(term, A)
        out = padd(out, pscale(term, coef))
    return out


def exp_series(A, nmax):
    out = {(0, 0, 0): sp.Integer(1)}
    term = {(0, 0, 0): sp.Integer(1)}
    for n in range(1, nmax + 1):
        term = pscale(pmul(term, A), sp.Rational(1, n))
        out = padd(out, term)
    return out


def build_chart(mirror):
    x = cospoly(0)
    y = cospoly(1)
    one = {(0, 0, 0): sp.Integer(1)}
    if mirror:
        C = 1 - 2 * p ** 2
        D = pscale(padd(x, y), -1)
        x2 = pmul(x, x)
        N = padd(pscale(padd(pscale(x2, 2), pscale(one, -1)), C),
                 pmul(y, padd(pscale(x, C), one, pscale(x2, -1))))
    else:
        C = 2 * p ** 2 - 1
        D = padd(x, y)
        x2 = pmul(x, x)
        N = padd(pscale(padd(pscale(x2, 2), pscale(one, -1)), C),
                 pmul(y, padd(pscale(x, C), pscale(one, -1), x2)))
    F = padd(N, pscale(D, -C))
    P = pscale(padd(one, pscale(x, -1)), sp.Rational(1, 2))
    Q = pscale(padd(one, pscale(y, -1)), sp.Rational(1, 2))
    w = padd(P, Q, pscale(pmul(P, Q), -1 / p ** 2))
    MB = NORD // 2 + 1
    sqrt1mw = binom_series(w, sp.Rational(1, 2), MB)
    inv_sqrt = binom_series(w, sp.Rational(-1, 2), MB)
    pow34 = binom_series(w, sp.Rational(-3, 4), MB)
    inv1m = binom_series(w, sp.Integer(-1), MB)
    # exponent residue: (4p/eps^2)(sqrt(1-w)-1) + p rho^2/2
    shifted = {}
    for (i, j, k), c in padd(sqrt1mw, pscale(one, -1)).items():
        if k - 2 >= 0:
            shifted[(i, j, k - 2)] = sp.expand(4 * p * c)
        else:
            raise RuntimeError("eps^-2 survives: %s" % str((i, j, k)))
    rho2 = {(2, 0, 0): p / 2, (0, 2, 0): p / 2}
    expo = padd(shifted, rho2)
    assert all(k > 0 for (i, j, k) in expo), "constant eps-order in expo"
    wcorr = exp_series(expo, NORD // 2)
    invz = {}
    for (i, j, k), c in inv_sqrt.items():
        if k + 2 < NORD:
            invz[(i, j, k + 2)] = sp.expand(c / (4 * p))
    KER = pmul(pmul(pow34, wcorr),
               padd(one, pscale(invz, sp.Rational(-3, 8))))
    rw1 = {(i, j, k + 2): sp.expand(c / (4 * p))
           for (i, j, k), c in inv_sqrt.items() if k + 2 < NORD}
    rw2 = {(i, j, k + 4): sp.expand(c / (16 * p ** 2))
           for (i, j, k), c in inv1m.items() if k + 4 < NORD}
    rw = padd(rw1, pscale(rw2, sp.Rational(-3, 2)))
    return D, F, rw, KER


def gauss_int(A):
    """integrate sigma,tau against e^{-p rho^2/2} over the plane;
    returns dict k -> coefficient (expr in p, times 2*pi/p etc)."""
    out = {}
    for (i, j, k), c in A.items():
        if i % 2 or j % 2:
            continue
        gi = sp.sqrt(2 * sp.pi / p) * sp.factorial2(i - 1) / p ** (i // 2) \
            if i > 0 else sp.sqrt(2 * sp.pi / p)
        gj = sp.sqrt(2 * sp.pi / p) * sp.factorial2(j - 1) / p ** (j // 2) \
            if j > 0 else sp.sqrt(2 * sp.pi / p)
        out[k] = out.get(k, 0) + c * gi * gj
    return out


CONV = 2 / (sp.sqrt(2 * sp.pi) * (4 * p) ** sp.Rational(3, 2))

print("building charts...", flush=True)
Dm, Fm, rwm, KERm = build_chart(True)
Ds, Fs, rws, KERs = build_chart(False)

MOMS = [
    ('mir', 'MD',   pmul(Dm, KERm),                     0, 1),
    ('mir', 'MF',   pmul(Fm, KERm),                     0, 1),
    ('mir', 'MD2r', pmul(pmul(pmul(Dm, Dm), rwm), KERm), 2,
     sp.Rational(1, 2)),
    ('mir', 'MDFr', pmul(pmul(pmul(Dm, Fm), rwm), KERm), 2,
     sp.Rational(1, 2)),
    ('main', 'muF', pmul(Fs, KERs),                     2, 1),
    ('main', 'nuD', pmul(pmul(pmul(Ds, Ds), rws), KERs), 2,
     sp.Rational(1, 2)),
    ('main', 'nuF', pmul(pmul(pmul(Ds, Fs), rws), KERs), 4,
     sp.Rational(1, 2)),
]

# closed forms: mirror in s (=p), C = 1-2s^2; main in c (=p), C = 2c^2-1
s = p
sq = sp.sqrt(2 * sp.pi)
CLOSED = {
    ('mir', 'MD'): (-2 * (sq / 4) * s ** sp.Rational(-5, 2),
                    sq * (7 * s ** 2 - 4) / (64 * s ** sp.Rational(11, 2))),
    ('mir', 'MF'): (4 * (1 - 2 * s ** 2) * (sq / 4) * s ** sp.Rational(-5, 2),
                    sq * (46 * s ** 4 - 23 * s ** 2 + 4)
                    / (32 * s ** sp.Rational(11, 2))),
    ('mir', 'MD2r'): ((sq / 8) * s ** sp.Rational(-7, 2),
                      sq * (4 - 27 * s ** 2)
                      / (256 * s ** sp.Rational(13, 2))),
    ('mir', 'MDFr'): (-(1 - 2 * s ** 2) * (sq / 4) * s ** sp.Rational(-7, 2),
                      sq * (-86 * s ** 4 + 43 * s ** 2 - 4)
                      / (128 * s ** sp.Rational(13, 2))),
    ('main', 'muF'): (-(2 * (2 * s ** 2 - 1) + 1) * (sq / 4)
                      * s ** sp.Rational(-7, 2),
                      3 * sq * (20 * s ** 4 - 17 * s ** 2 + 4)
                      / (128 * s ** sp.Rational(13, 2))),
    ('main', 'nuD'): ((sq / 8) * s ** sp.Rational(-7, 2),
                      sq * (4 - 27 * s ** 2)
                      / (256 * s ** sp.Rational(13, 2))),
    ('main', 'nuF'): (-(2 * (2 * s ** 2 - 1) + 1) * (sq / 16)
                      * s ** sp.Rational(-9, 2),
                      sq * (172 * s ** 4 - 79 * s ** 2 + 12)
                      / (512 * s ** sp.Rational(15, 2))),
}

allok = True
for kind, nm, poly, k0, fac in MOMS:
    momk = gauss_int(poly)
    lead = sp.simplify(CONV * fac * momk.get(k0, 0))
    nxt = sp.simplify(CONV * fac * momk.get(k0 + 2, 0))
    cl, cn = CLOSED[(kind, nm)]
    d1 = sp.simplify(lead - cl)
    d2 = sp.simplify(nxt - cn)
    ok1 = d1 == 0
    ok2 = d2 == 0
    allok = allok and ok1 and ok2
    print("  %-4s %-5s lead %s  next %s" % (kind, nm,
          "== closed form" if ok1 else "MISMATCH: %s" % d1,
          "== closed form" if ok2 else "MISMATCH: %s" % d2), flush=True)
    # also check odd/parity structural zeros: k0-2 and k0+1 absent
    if momk.get(k0 - 2, 0) != 0 and sp.simplify(momk.get(k0 - 2, 0)) != 0:
        print("    WARNING: nonzero coefficient below k0!", flush=True)
        allok = False

print("STAGE 1: %s" % ("ALL SEVEN lead+next REPRODUCED SYMBOLICALLY"
                       if allok else "MISMATCH FOUND"), flush=True)
