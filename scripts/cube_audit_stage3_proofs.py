"""INTERNAL CUBE AUDIT - stage 3:
(1) EXACT-arithmetic (Fraction) proof that the L3 structural claim
    k >= i+j is false for the actual truncated integrand: the MD
    mirror integrand carries sigma^4 eps^2 (and peers) with an exact
    nonzero rational coefficient at rational p.
(2) census of the expo polynomial: verify the true invariant
    k = i+j-2 per expo monomial (basis of a corrected L3').
(3) direct model-error quadrature at two mirror cells: true kernel
    (Bessel) rectangle integral vs poly-plane value minus true
    completion of the poly -> measured model error vs the G sources.
(4) independent quadrature of the U_D truths at (2.9,15):
    B_K = int_B K (m-units) and m_true = <D> (whole torus).
"""
import math
from fractions import Fraction as Fr

import mpmath as mp

print("=== CUBE AUDIT stage 3 ===", flush=True)

# ---------- (1)+(2) exact Fraction engine, NORD=6 ------------------
NORD = 6
PV = Fr(29, 50)   # rational p inside the mirror zone


def pmul(A, B, nord=NORD):
    C = {}
    for (i1, j1, k1), c1 in A.items():
        for (i2, j2, k2), c2 in B.items():
            k = k1 + k2
            if k >= nord:
                continue
            key = (i1 + i2, j1 + j2, k)
            C[key] = C.get(key, Fr(0)) + c1 * c2
    return {k: c for k, c in C.items() if c != 0}


def padd(*polys):
    C = {}
    for A in polys:
        for k, c in A.items():
            C[k] = C.get(k, Fr(0)) + c
    return {k: c for k, c in C.items() if c != 0}


def pscale(A, s):
    return {k: s * c for k, c in A.items()}


def cospoly(vi):
    out = {}
    m = 0
    while 2 * m < NORD:
        key = (2 * m, 0, 2 * m) if vi == 0 else (0, 2 * m, 2 * m)
        out[key] = Fr((-1) ** m, math.factorial(2 * m))
        m += 1
    return out


def binom_series(A, num, den, mmax):
    """(1-A)^{num/den} exact binomial series."""
    out = {(0, 0, 0): Fr(1)}
    term = {(0, 0, 0): Fr(1)}
    coef = Fr(1)
    alpha = Fr(num, den)
    for m in range(1, mmax + 1):
        coef *= (alpha - m + 1) / m
        term = pmul(term, A)
        out = padd(out, pscale(term, coef * (-1) ** m))
    return out


def exp_series(A, nmax):
    out = {(0, 0, 0): Fr(1)}
    term = {(0, 0, 0): Fr(1)}
    for n in range(1, nmax + 1):
        term = pscale(pmul(term, A), Fr(1, n))
        out = padd(out, term)
    return out


one = {(0, 0, 0): Fr(1)}
x = cospoly(0)
y = cospoly(1)
D = pscale(padd(x, y), Fr(-1))          # mirror chart
P = pscale(padd(one, pscale(x, Fr(-1))), Fr(1, 2))
Q = pscale(padd(one, pscale(y, Fr(-1))), Fr(1, 2))
w = padd(P, Q, pscale(pmul(P, Q), Fr(-1) / PV ** 2))
MB = NORD // 2 + 1
sqrt1mw = binom_series(w, 1, 2, MB)
inv_sqrt = binom_series(w, -1, 2, MB)
pow34 = binom_series(w, -3, 4, MB)
shifted = {}
for (i, j, k), c in padd(sqrt1mw, pscale(one, Fr(-1))).items():
    assert k >= 2
    shifted[(i, j, k - 2)] = 4 * PV * c
expo = padd(shifted, {(2, 0, 0): PV / 2, (0, 2, 0): PV / 2})
print("(2) expo census at p=%s (exact):" % PV, flush=True)
inv_ok = True
for (i, j, k), c in sorted(expo.items()):
    tag = "k=i+j-2 OK" if k == i + j - 2 else "INVARIANT VIOLATION"
    if k != i + j - 2:
        inv_ok = False
    print("    expo monomial s^%d t^%d e^%d coeff %s  [%s]"
          % (i, j, k, c, tag), flush=True)
print("    expo invariant k = i+j-2 (each monomial): %s"
      % ("HOLDS" if inv_ok else "FAILS"), flush=True)

wcorr = exp_series(expo, NORD // 2)
invz = {(i, j, k + 2): c / (4 * PV)
        for (i, j, k), c in inv_sqrt.items() if k + 2 < NORD}
KER = pmul(pmul(pow34, wcorr),
           padd(one, pscale(invz, Fr(-3, 8))))
MD_int = pmul(D, KER)
print("\n(1) L3 exact counterexamples in the MD mirror integrand"
      " (NORD=6, p=29/50):", flush=True)
nviol = 0
for (i, j, k), c in sorted(MD_int.items()):
    if k < i + j and c != 0:
        nviol += 1
        if k <= 2:
            print("    s^%d t^%d e^%d  coeff = %s  (k < i+j, exact"
                  " nonzero)" % (i, j, k, c), flush=True)
print("    total exact violations at NORD=6: %d" % nviol, flush=True)

# ---------- (3) model-error quadrature at mirror cells -------------
print("\n(3) model-error measurement (mirror chart):", flush=True)
mp.mp.dps = 20
R = mp.mpf('1.2')


def mirror_scaled_moment(tt, bb, which):
    t = mp.mpf(tt); beta = mp.mpf(bb)
    c = mp.cos(t / 4); s4 = mp.sin(t / 4)
    zs4 = 4 * beta * s4

    def core(s, a):
        Pq = mp.sin(s / 2) ** 2; Qq = mp.sin(a / 2) ** 2
        R2 = 4 * c * c * (1 - Pq) * (1 - Qq) + 4 * s4 * s4 * Pq * Qq
        z = 2 * beta * mp.sqrt(R2)
        K_res = 2 * beta ** mp.mpf('2.5') \
            * (mp.besseli(1, z) / mp.e ** z / z) * mp.e ** (z - zs4)
        Dv = 2 * (1 - Pq - Qq)
        CC = 2 * c * c - 1
        N = CC * mp.cos(2 * s) + mp.cos(a) * (CC * mp.cos(s) - 1
                                              + mp.cos(s) ** 2)
        Fv = N - CC * Dv
        return K_res * (Dv if which == 'MD' else Fv)
    xs = [mp.pi - R, mp.pi - R / 2, mp.pi]
    return 4 * mp.quad(lambda s: mp.quad(lambda a: core(s, a), xs), xs)


# float engine (NORD=16) copied minimal from stage 2 for the poly
import importlib.util
spec = importlib.util.spec_from_file_location(
    "st2", r"audit_stage2_polyonly.py")

# instead of importing, rebuild inline (float engine, NORD=16)
NORDf = 16


def fmul(A, B):
    C = {}
    for (i1, j1, k1), c1 in A.items():
        for (i2, j2, k2), c2 in B.items():
            k = k1 + k2
            if k >= NORDf:
                continue
            key = (i1 + i2, j1 + j2, k)
            C[key] = C.get(key, 0.0) + c1 * c2
    return C


def fadd(*polys):
    C = {}
    for A in polys:
        for kk, c in A.items():
            C[kk] = C.get(kk, 0.0) + c
    return C


def fscale(A, s):
    return {kk: s * c for kk, c in A.items()}


def fcos(vi):
    out = {}
    m = 0
    f = 1.0
    while 2 * m < NORDf:
        key = (2 * m, 0, 2 * m) if vi == 0 else (0, 2 * m, 2 * m)
        out[key] = ((-1.0) ** m) / f
        m += 1
        f *= (2 * m - 1) * (2 * m)
    return out


def fbinom(A, alpha, mmax):
    out = {(0, 0, 0): 1.0}
    term = {(0, 0, 0): 1.0}
    coef = 1.0
    for m in range(1, mmax + 1):
        coef *= (alpha - m + 1) / m
        term = fmul(term, A)
        out = fadd(out, fscale(term, coef * (-1.0) ** m))
    return out


def fexp(A, nmax):
    out = {(0, 0, 0): 1.0}
    term = {(0, 0, 0): 1.0}
    for n in range(1, nmax + 1):
        term = fscale(fmul(term, A), 1.0 / n)
        out = fadd(out, term)
    return out


def fbuild_mir(pv):
    xf = fcos(0); yf = fcos(1)
    onef = {(0, 0, 0): 1.0}
    Df = fscale(fadd(xf, yf), -1.0)
    Cc = 1 - 2 * pv * pv
    x2 = fmul(xf, xf)
    Nf = fadd(fscale(fadd(fscale(x2, 2.0), fscale(onef, -1.0)), Cc),
              fmul(yf, fadd(fscale(xf, Cc), onef, fscale(x2, -1.0))))
    Ff = fadd(Nf, fscale(Df, -Cc))
    Pf = fscale(fadd(onef, fscale(xf, -1.0)), 0.5)
    Qf = fscale(fadd(onef, fscale(yf, -1.0)), 0.5)
    wf = fadd(Pf, Qf, fscale(fmul(Pf, Qf), -1.0 / pv ** 2))
    MBf = NORDf // 2 + 1
    sq = fbinom(wf, 0.5, MBf)
    isq = fbinom(wf, -0.5, MBf)
    p34 = fbinom(wf, -0.75, MBf)
    sh = {}
    for (i, j, k), c in fadd(sq, fscale(onef, -1.0)).items():
        if k >= 2:
            sh[(i, j, k - 2)] = 4 * pv * c
    ex = fadd(sh, {(2, 0, 0): pv / 2, (0, 2, 0): pv / 2})
    ex = {kk: c for kk, c in ex.items()
          if not (kk[2] == 0 and abs(c) < 1e-12)}
    wc = fexp(ex, NORDf // 2)
    iz = {(i, j, k + 2): c / (4 * pv)
          for (i, j, k), c in isq.items() if k + 2 < NORDf}
    KERf = fmul(fmul(p34, wc), fadd(onef, fscale(iz, -3.0 / 8)))
    return Df, Ff, KERf


SQ2PI = math.sqrt(2 * math.pi)


def polyval(A, sg, ta, ep):
    return sum(c * sg ** i * ta ** j * ep ** k
               for (i, j, k), c in A.items())


for tt, which in [('2.6', 'MD'), ('2.9', 'MF')]:
    t = float(tt)
    beta = 15.0
    s4 = math.sin(t / 4)
    pv = s4
    Df, Ff, KERf = fbuild_mir(pv)
    poly = fmul(Df if which == 'MD' else Ff, KERf)
    convf = 2 / (SQ2PI * (4 * pv) ** 1.5)
    # poly-plane series value at beta
    cs = {}
    for (i, j, k), c in poly.items():
        if i % 2 or j % 2:
            continue
        gi = math.sqrt(2 * math.pi / pv)
        m = i
        while m > 0:
            gi *= (m - 1) / pv
            m -= 2
        gj = math.sqrt(2 * math.pi / pv)
        m = j
        while m > 0:
            gj *= (m - 1) / pv
            m -= 2
        cs[k] = cs.get(k, 0.0) + c * gi * gj
    poly_plane = convf * sum(cc * beta ** (-k / 2.0)
                             for k, cc in cs.items())
    # true completion of the poly: plane minus rectangle (numeric)
    eps = 1 / math.sqrt(beta)
    Rs = 1.2 * math.sqrt(beta)

    def integrand(sg, ta):
        return polyval(poly, sg, ta, eps) \
            * math.exp(-pv * (sg * sg + ta * ta) / 2)
    mp.mp.dps = 15
    rect = mp.quad(lambda sg: mp.quad(lambda ta: integrand(
        float(sg), float(ta)), [0, Rs / 2, Rs]), [0, Rs / 2, Rs]) * 4
    poly_rect = convf * float(rect)
    completion_true = poly_plane - poly_rect
    mp.mp.dps = 20
    v_true = float(mirror_scaled_moment(tt, 15, which))
    modelerr = v_true - poly_rect
    zs1 = 4 * pv * beta
    lead = convf * cs.get(0, 0.0)
    g_a_abs = (4.94 / zs1 ** 3
               + 0.34 * (1.1 / zs1) / zs1 ** 2) * abs(lead)
    e1_abs = ((15 / 128) / zs1 ** 2 + 1.02 / zs1 ** 3) * abs(lead)
    print("  %s t=%s beta=15: v_true %.6f | poly_rect %.6f |"
          % (which, tt, v_true, poly_rect), flush=True)
    print("     poly_plane %.6f  completion_true %+.6f (bucket units"
          " %+.3f; committed fold bound must exceed |this|)"
          % (poly_plane, completion_true, completion_true * 225),
          flush=True)
    print("     MODEL ERROR v_true - poly_rect = %+.3e -> bucket"
          " units %+.4f" % (modelerr, modelerr * 225), flush=True)
    print("     G covers: g_a(committed) %.4f bucket | frozen-eps1"
          " (omitted) %.4f bucket | g_d alloc %.4f"
          % (g_a_abs * 225, e1_abs * 225, 0.02 * abs(lead)),
          flush=True)

# ---------- (4) U_D truths by direct quadrature --------------------
print("\n(4) U_D truths at (2.9,15), m-units, dps=15:", flush=True)
mp.mp.dps = 15
t = mp.mpf('2.9'); beta = mp.mpf(15)
c = mp.cos(t / 4); s4 = mp.sin(t / 4); zs = 4 * beta * c


def K_res(s, a):
    Pq = mp.sin(s / 2) ** 2; Qq = mp.sin(a / 2) ** 2
    R2 = 4 * c * c * (1 - Pq) * (1 - Qq) + 4 * s4 * s4 * Pq * Qq
    z = 2 * beta * mp.sqrt(R2)
    return 2 * beta ** mp.mpf('2.5') \
        * (mp.besseli(1, z) / mp.e ** z / z) * mp.e ** (z - zs)


BK = 4 * mp.quad(lambda s: mp.quad(lambda a: K_res(s, a),
                                   [0, mp.mpf('0.6'), mp.mpf('1.2')]),
                 [0, mp.mpf('0.6'), mp.mpf('1.2')])
print("  int_B K (B = [-1.2,1.2]^2) = %s ; committed bench slack"
      " implies 1.3571 ; 2x = %s" % (mp.nstr(BK, 6),
                                     mp.nstr(2 * BK, 6)), flush=True)
KT = 4 * mp.quad(lambda s: mp.quad(lambda a: K_res(s, a),
                                   [0, mp.mpf('1.2'), 2, mp.pi]),
                 [0, mp.mpf('1.2'), 2, mp.pi])
print("  int_torus K = %s ; 2x = %s  (U_D committed = 2.9326)"
      % (mp.nstr(KT, 6), mp.nstr(2 * KT, 6)), flush=True)


def KD_res(s, a):
    Pq = mp.sin(s / 2) ** 2; Qq = mp.sin(a / 2) ** 2
    return K_res(s, a) * 2 * (1 - Pq - Qq)


MT = 4 * mp.quad(lambda s: mp.quad(lambda a: KD_res(s, a),
                                   [0, mp.mpf('1.2'), 2, mp.pi]),
                 [0, mp.mpf('1.2'), 2, mp.pi])
print("  <D> true (m-units) = %s  (cascade1 bench: 2.5649;"
      " m_low 1.79657)" % mp.nstr(MT, 6), flush=True)
print("\nstage 3 complete.", flush=True)
