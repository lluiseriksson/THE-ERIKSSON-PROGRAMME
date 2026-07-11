"""INTERNAL CUBE AUDIT - stage 2: numeric audit at NORD=16 (own
dict engine, float coefficients).

(a) monomial census: test the structural claim k >= i+j (Codex L3)
    on every integrand monomial; compute the worst beta-exponent
    q = 2 + (k0-k)/2 + (max(i,j)-1)/2 (L4 input).
(b) extract c2..c6 (exact orders within NORD=16) at every judged pv;
    reproduce the committed script's B2 values; measure the
    intra-truncation tail sum_{j>=4} |c_j|/beta1^{j-2} vs the g_d
    allocation 0.02*|lead|.
(c) the Gaussian <w>-moment leading coefficient vs the claimed
    1.1/(4 p beta).
(d) comp_fold reproduction + numeric beta-monotonicity on a grid.
(e) frozen-eps1 source size (omitted from G) vs g_d.
(f) domination table from the committed judge transcripts, with
    committed B2 and with a corrected B2.
(g) M_sharp reproduction + U_D piece analysis vs the committed
    cascade1 bench truths.
"""
import hashlib
import json
import math
import re
import sys

print("=== CUBE AUDIT stage 2: numeric, own engine, NORD=16 ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("python %s" % sys.version.split()[0], flush=True)

NORD = 16
SCRIPTS = r"C:\Users\lluis\AppData\Local\Temp\eriksson-push2\scripts"

# ---------------- dict engine (float coefficients) ----------------


def pmul(A, B, nord=NORD):
    C = {}
    for (i1, j1, k1), c1 in A.items():
        for (i2, j2, k2), c2 in B.items():
            k = k1 + k2
            if k >= nord:
                continue
            key = (i1 + i2, j1 + j2, k)
            C[key] = C.get(key, 0.0) + c1 * c2
    return C


def padd(*polys):
    C = {}
    for A in polys:
        for k, c in A.items():
            C[k] = C.get(k, 0.0) + c
    return C


def pscale(A, s):
    return {k: s * c for k, c in A.items()}


def cospoly(vi):
    out = {}
    m = 0
    f = 1.0
    while 2 * m < NORD:
        key = (2 * m, 0, 2 * m) if vi == 0 else (0, 2 * m, 2 * m)
        out[key] = ((-1.0) ** m) / f
        m += 1
        f *= (2 * m - 1) * (2 * m)
    return out


def binom_series(A, alpha, mmax):
    out = {(0, 0, 0): 1.0}
    term = {(0, 0, 0): 1.0}
    coef = 1.0
    for m in range(1, mmax + 1):
        coef *= (alpha - m + 1) / m
        term = pmul(term, A)
        out = padd(out, pscale(term, coef * (-1.0) ** m))
    return out


def exp_series(A, nmax):
    out = {(0, 0, 0): 1.0}
    term = {(0, 0, 0): 1.0}
    for n in range(1, nmax + 1):
        term = pscale(pmul(term, A), 1.0 / n)
        out = padd(out, term)
    return out


def build_chart(mirror, pv):
    x = cospoly(0)
    y = cospoly(1)
    one = {(0, 0, 0): 1.0}
    if mirror:
        C = 1 - 2 * pv * pv
        D = pscale(padd(x, y), -1.0)
        x2 = pmul(x, x)
        N = padd(pscale(padd(pscale(x2, 2.0), pscale(one, -1.0)), C),
                 pmul(y, padd(pscale(x, C), one, pscale(x2, -1.0))))
    else:
        C = 2 * pv * pv - 1
        D = padd(x, y)
        x2 = pmul(x, x)
        N = padd(pscale(padd(pscale(x2, 2.0), pscale(one, -1.0)), C),
                 pmul(y, padd(pscale(x, C), pscale(one, -1.0), x2)))
    F = padd(N, pscale(D, -C))
    P = pscale(padd(one, pscale(x, -1.0)), 0.5)
    Q = pscale(padd(one, pscale(y, -1.0)), 0.5)
    w = padd(P, Q, pscale(pmul(P, Q), -1.0 / pv ** 2))
    MB = NORD // 2 + 1
    sqrt1mw = binom_series(w, 0.5, MB)
    inv_sqrt = binom_series(w, -0.5, MB)
    pow34 = binom_series(w, -0.75, MB)
    inv1m = binom_series(w, -1.0, MB)
    shifted = {}
    for (i, j, k), c in padd(sqrt1mw, pscale(one, -1.0)).items():
        if abs(c) < 1e-300:
            continue
        assert k - 2 >= 0, "eps^-2 survives"
        shifted[(i, j, k - 2)] = 4 * pv * c
    rho2 = {(2, 0, 0): pv / 2, (0, 2, 0): pv / 2}
    expo = padd(shifted, rho2)
    # structural zero: no k = 0 term may survive
    z0 = max((abs(c) for (i, j, k), c in expo.items() if k == 0),
             default=0.0)
    assert z0 < 1e-12, "expo has surviving eps^0 term %g" % z0
    expo = {k: c for k, c in expo.items()
            if not (k[2] == 0 and abs(c) < 1e-12)}
    wcorr = exp_series(expo, NORD // 2)
    invz = {(i, j, k + 2): c / (4 * pv)
            for (i, j, k), c in inv_sqrt.items() if k + 2 < NORD}
    KER = pmul(pmul(pow34, wcorr),
               padd(one, pscale(invz, -3.0 / 8)))
    rw1 = {(i, j, k + 2): c / (4 * pv)
           for (i, j, k), c in inv_sqrt.items() if k + 2 < NORD}
    rw2 = {(i, j, k + 4): c / (16 * pv ** 2)
           for (i, j, k), c in inv1m.items() if k + 4 < NORD}
    rw = padd(rw1, pscale(rw2, -1.5))
    return D, F, rw, KER, w


SQ2PI = math.sqrt(2 * math.pi)


def gauss_1d(i, pv):
    if i % 2:
        return 0.0
    g = math.sqrt(2 * math.pi / pv)
    m = i
    while m > 0:
        g *= (m - 1) / pv
        m -= 2
    return g


def gauss_int_series(A, pv):
    out = {}
    for (i, j, k), c in A.items():
        if i % 2 or j % 2:
            continue
        out[k] = out.get(k, 0.0) + c * gauss_1d(i, pv) * gauss_1d(j, pv)
    return out


def conv(pv):
    return 2 / (SQ2PI * (4 * pv) ** 1.5)


def integrands(pv):
    Dm, Fm, rwm, KERm, wm = build_chart(True, pv)
    Ds, Fs, rws, KERs, ws = build_chart(False, pv)
    return {
        ('mir', 'MD'): (pmul(Dm, KERm), 0, 1.0, wm, KERm),
        ('mir', 'MF'): (pmul(Fm, KERm), 0, 1.0, wm, KERm),
        ('mir', 'MD2r'): (pmul(pmul(pmul(Dm, Dm), rwm), KERm), 2, 0.5,
                          wm, KERm),
        ('mir', 'MDFr'): (pmul(pmul(pmul(Dm, Fm), rwm), KERm), 2, 0.5,
                          wm, KERm),
        ('main', 'muF'): (pmul(Fs, KERs), 2, 1.0, ws, KERs),
        ('main', 'nuD'): (pmul(pmul(pmul(Ds, Ds), rws), KERs), 2, 0.5,
                          ws, KERs),
        ('main', 'nuF'): (pmul(pmul(pmul(Ds, Fs), rws), KERs), 4, 0.5,
                          ws, KERs),
    }


# ---------------- (a)+(b)+(c): per-pv extraction and census --------
BETA1 = 15.0
R1C_15 = 1.2 * math.sqrt(BETA1)

PVS = {}   # (kind, pv-label) -> pv
PVS[('mir', 'zone')] = 0.5801
PVS[('mir', 't2.6')] = math.sin(2.6 / 4)
PVS[('mir', 't2.9')] = math.sin(2.9 / 4)
PVS[('main', 'zone')] = 0.7071
PVS[('main', 't0.5')] = math.cos(0.5 / 4)
PVS[('main', 't1.5')] = math.cos(1.5 / 4)
PVS[('main', 't2.9')] = math.cos(2.9 / 4)

MIR_NAMES = ['MD', 'MF', 'MD2r', 'MDFr']
MAIN_NAMES = ['muF', 'nuD', 'nuF']


def tail_moments(pv, R, nt=44):
    E = math.exp(-pv * R * R / 2)
    T = [E / (pv * R), E / pv]
    for k in range(2, nt):
        T.append(R ** (k - 1) * E / pv + (k - 1) / pv * T[k - 2])
    G = [math.sqrt(2 * math.pi / pv), 2 / pv]
    for m in range(2, nt):
        G.append((m - 1) / pv * G[m - 2])
    return T, G


def comp_fold(poly, k0, fac, pv, beta):
    R = 1.2 * math.sqrt(beta)
    T, G = tail_moments(pv, R)
    tot = 0.0
    for (i, j, k), a in poly.items():
        tot += abs(a) * beta ** ((k0 - k) / 2) \
            * (2 * T[i] * G[j] + G[i] * 2 * T[j])
    return conv(pv) * fac * tot * beta ** 2


def census(poly, k0):
    viol = 0
    worst_gap = 0
    worst_mono = None
    qmax = -99.0
    qmono = None
    for (i, j, k), a in poly.items():
        if abs(a) < 1e-14:
            continue
        if k < i + j:
            viol += 1
            if (i + j) - k > worst_gap:
                worst_gap = (i + j) - k
                worst_mono = (i, j, k, a)
        q = 2 + (k0 - k) / 2 + (max(i, j) - 1) / 2
        if q > qmax:
            qmax = q
            qmono = (i, j, k, a)
    return viol, worst_gap, worst_mono, qmax, qmono


RESULTS = {}
print("\n--- per-pv extraction, census, comp ---", flush=True)
for (kind, lab), pv in PVS.items():
    ints = integrands(pv)
    names = MIR_NAMES if kind == 'mir' else MAIN_NAMES
    for nm in names:
        poly, k0, fac, w, KERc = ints[(kind, nm)]
        ser = gauss_int_series(poly, pv)
        cf = conv(pv) * fac
        cs = []
        jj = 0
        while k0 + 2 * jj < NORD:
            cs.append(cf * ser.get(k0 + 2 * jj, 0.0))
            jj += 1
        below = max((abs(ser.get(k, 0.0)) for k in range(0, k0, 2)),
                    default=0.0) * cf
        viol, wg, wm, qmax, qm = census(poly, k0)
        cmp15 = comp_fold(poly, k0, fac, pv, 15.0)
        # beta-monotonicity of the fold on a grid
        grid = [15 + 0.5 * n for n in range(0, 41)] + \
               [40, 50, 60, 80, 100, 150, 200, 300]
        vals = [comp_fold(poly, k0, fac, pv, b) for b in grid]
        mono = all(vals[n + 1] <= vals[n] * (1 + 1e-12)
                   for n in range(len(vals) - 1))
        RESULTS[(kind, lab, nm)] = dict(
            pv=pv, cs=cs, below=below, viol=viol, worst_gap=wg,
            worst_mono=repr(wm), qmax=qmax, qmono=repr(qm),
            comp15=cmp15, mono=mono, nterms=len(poly))
        print(" %s %s %-5s pv=%.6f terms=%d  below-k0 resid %.2e"
              % (kind, lab, nm, pv, len(poly), below), flush=True)
        print("   c0..c%d: %s" % (len(cs) - 1,
              " ".join("%+.6g" % c for c in cs)), flush=True)
        print("   L3 census: %d monomials with k < i+j (worst gap %d: %s)"
              % (viol, wg, wm), flush=True)
        print("   qmax = %.2f at %s ; 0.72*p*15 = %.2f ; comp(15) = %.5g ;"
              " grid-monotone: %s"
              % (qmax, qm, 0.72 * pv * 15, cmp15, mono), flush=True)

# ---------------- (c) <w> Gaussian moment --------------------------
print("\n--- <w> moment (claim: <w> <= 1.1/(4 p beta)) ---", flush=True)
for kind in ['mir', 'main']:
    pv = PVS[(kind, 'zone')]
    ints = integrands(pv)
    nm = MIR_NAMES[0] if kind == 'mir' else MAIN_NAMES[0]
    poly, k0, fac, w, KERc = ints[(kind, nm)]
    num = gauss_int_series(pmul(w, KERc), pv)
    den = gauss_int_series(KERc, pv)
    # <w> = (num series)/(den series); leading = num[2]/den[0] * eps^2
    r1 = num.get(2, 0.0) / den.get(0, 0.0)
    print("  %s pv=%.4f: <w> leading = %.6f eps^2 = %.4f/(4 p beta)"
          " (claimed 1.1)" % (kind, pv, r1, r1 * 4 * pv), flush=True)
    # next order for the ball/(1-w) correction sense
    r2 = (num.get(4, 0.0) - r1 * den.get(2, 0.0)) / den.get(0, 0.0)
    print("     next order coeff (eps^4): %.4f -> at beta=15 rel corr %+.3f"
          % (r2, r2 / 15 / (r1)), flush=True)

# ---------------- (d) T-recursion upper-bound check ----------------
print("\n--- tail-moment recursion vs quadrature (mpmath) ---",
      flush=True)
import mpmath as mp
mp.mp.dps = 25
pvt = 0.5801
Rt = R1C_15
Tt, Gt = tail_moments(pvt, Rt)
okT = True
for k in range(0, 12):
    exact = mp.quad(lambda x: x ** k * mp.e ** (-pvt * x * x / 2),
                    [Rt, mp.inf])
    ub = Tt[k]
    ok = ub >= exact * (1 - 1e-12)
    tight = float(ub / exact)
    if not ok:
        okT = False
    print("  T_%d: recursion %.6e  exact %.6e  ratio %.4f %s"
          % (k, ub, float(exact), tight, "OK" if ok else "VIOLATION"),
          flush=True)
Gex_ok = True
for m in range(0, 8):
    exact = mp.quad(lambda x: abs(x) ** m * mp.e ** (-pvt * x * x / 2),
                    [-mp.inf, 0, mp.inf])
    if abs(float(exact) - Gt[m]) / float(exact) > 1e-12:
        Gex_ok = False
print("  T-recursion upper bounds: %s ; Gbar exact: %s"
      % ("OK" if okT else "FAIL", "OK" if Gex_ok else "FAIL"),
      flush=True)

# ---------------- (b') reproduce committed B2 ----------------------
print("\n--- B2 reproduction (committed formula, my engine) ---",
      flush=True)


def bucket_committed(cs, lead, pv, nu_like, comp):
    c2 = abs(cs[2]); c3 = abs(cs[3])
    zs1 = 4 * BETA1 * pv
    wbar = 1.1 / (4 * pv * BETA1)
    g_a = (4.94 / zs1 ** 3 + 0.34 * wbar / zs1 ** 2) * BETA1 ** 2
    g_bc = 0.0
    if nu_like:
        g_bc = (1.23 / zs1 ** 2 + 1.37 * wbar / zs1 ** 3
                + 12.5 / zs1 ** 4) * BETA1 ** 2
    g_d = 0.02
    G = abs(lead) * (g_a + g_bc + g_d)
    return c2 + c3 / BETA1 + G + comp


NU = {'MD2r', 'MDFr', 'nuD', 'nuF'}
B2_MINE = {}
for (kind, lab, nm), rr in sorted(RESULTS.items()):
    cs = rr['cs']
    b2 = bucket_committed(cs, cs[0], rr['pv'], nm in NU, rr['comp15'])
    B2_MINE[(kind, lab, nm)] = b2
    print("  B2 %s %s %-5s = %.5g   (c2 %.5g c3 %.5g comp %.5g)"
          % (kind, lab, nm, b2, abs(cs[2]), abs(cs[3]), rr['comp15']),
          flush=True)

# ---------------- (e)+(f) corrected B2 and domination --------------
print("\n--- corrected-B2 ingredients ---", flush=True)


def bucket_corrected(cs, pv, nu_like, comp):
    """B2 with the audit corrections:
    - conversion via mom_max = sum |c_j|/beta1^j (not |lead|);
    - <w> coefficient 2.0 (measured ~1.9x the claimed 1.1) + 10%;
    - frozen-eps1 source added: (15/128)/zs^2 + 1.02/zs^3 relative,
      with bracket back-conversion x1.02;
    - intra-truncation orders sum_{j>=4} |c_j|/beta1^{j-2} added,
      plus a geometric estimate of the beyond-NORD series tail;
    - g_d retained at 0.02 for the exponentially-flat slivers.
    """
    mom_max = sum(abs(c) / BETA1 ** j for j, c in enumerate(cs))
    zs1 = 4 * BETA1 * pv
    wbar = 2.2 / (4 * pv * BETA1)
    g_a = (4.94 / zs1 ** 3 + 0.34 * wbar / zs1 ** 2) * BETA1 ** 2
    g_e1 = ((15 / 128) / zs1 ** 2 + 1.02 / zs1 ** 3) * 1.02 * BETA1 ** 2
    g_bc = 0.0
    if nu_like:
        g_bc = (1.23 / zs1 ** 2 + 1.37 * wbar / zs1 ** 3
                + 12.5 / zs1 ** 4) * BETA1 ** 2
    g_d = 0.02
    G = mom_max * (g_a + g_e1 + g_bc + g_d)
    ctail = sum(abs(cs[j]) / BETA1 ** (j - 2) for j in range(4, len(cs)))
    if len(cs) >= 3 and abs(cs[-2]) > 0:
        rho = abs(cs[-1]) / abs(cs[-2])
        if rho / BETA1 < 0.9:
            ctail += abs(cs[-1]) / BETA1 ** (len(cs) - 3) \
                * (rho / BETA1) / (1 - rho / BETA1)
    return abs(cs[2]) + abs(cs[3]) / BETA1 + ctail + G + comp


def load_table(fn, ncols):
    tab = {}
    pat = re.compile(r"^\s+([\d.]+)\s+(\d+)\s\|"
                     + r"\s*([+-][\d.]+)" * ncols)
    for line in open(fn):
        m_ = pat.match(line)
        if m_:
            tab[(m_.group(1), int(m_.group(2)))] = \
                [float(m_.group(3 + i)) for i in range(ncols)]
    return tab


tmir = load_table(SCRIPTS + r"\cascade3_judges_transcript.txt", 4)
tmain = load_table(SCRIPTS + r"\cascade3b_judges_transcript.txt", 3)
assert len(tmir) == 9 and len(tmain) == 9
print("  judge tables parsed: mirror 9 rows, main 9 rows", flush=True)

# closed-form lead/next evaluators (verified symbolically in stage 1)


def lead_next(kind, nm, pv):
    s = pv
    r = math.sqrt
    if kind == 'mir':
        C = 1 - 2 * s * s
        if nm == 'MD':
            return (-2 * SQ2PI / 4 * s ** -2.5,
                    SQ2PI * (7 * s ** 2 - 4) / (64 * s ** 5.5))
        if nm == 'MF':
            return (4 * C * SQ2PI / 4 * s ** -2.5,
                    SQ2PI * (46 * s ** 4 - 23 * s ** 2 + 4)
                    / (32 * s ** 5.5))
        if nm == 'MD2r':
            return (SQ2PI / 8 * s ** -3.5,
                    SQ2PI * (4 - 27 * s ** 2) / (256 * s ** 6.5))
        if nm == 'MDFr':
            return (-C * SQ2PI / 4 * s ** -3.5,
                    SQ2PI * (-86 * s ** 4 + 43 * s ** 2 - 4)
                    / (128 * s ** 6.5))
    else:
        C = 2 * s * s - 1
        if nm == 'muF':
            return (-(2 * C + 1) * SQ2PI / 4 * s ** -3.5,
                    3 * SQ2PI * (20 * s ** 4 - 17 * s ** 2 + 4)
                    / (128 * s ** 6.5))
        if nm == 'nuD':
            return (SQ2PI / 8 * s ** -3.5,
                    SQ2PI * (4 - 27 * s ** 2) / (256 * s ** 6.5))
        if nm == 'nuF':
            return (-(2 * C + 1) * SQ2PI / 16 * s ** -4.5,
                    SQ2PI * (172 * s ** 4 - 79 * s ** 2 + 12)
                    / (512 * s ** 7.5))
    raise KeyError


print("\n--- domination: committed B2 and corrected B2 ---", flush=True)
CELLS = ([('mir', 't2.6', '2.6', nm) for nm in MIR_NAMES]
         + [('mir', 't2.9', '2.9', nm) for nm in MIR_NAMES]
         + [('main', 't0.5', '0.5', nm) for nm in MAIN_NAMES]
         + [('main', 't1.5', '1.5', nm) for nm in MAIN_NAMES]
         + [('main', 't2.9', '2.9', nm) for nm in MAIN_NAMES])
okc = True
okx = True
for kind, lab, tt, nm in CELLS:
    pv = PVS[(kind, lab)]
    rr = RESULTS[(kind, lab, nm)]
    cs = rr['cs']
    lead, nxt = lead_next(kind, nm, pv)
    # engine self-check vs closed forms
    assert abs(cs[0] - lead) < 1e-9 * max(1, abs(lead)), (nm, cs[0], lead)
    assert abs(cs[1] - nxt) < 1e-9 * max(1, abs(nxt)), (nm, cs[1], nxt)
    b2c = bucket_committed(cs, cs[0], pv, nm in NU, rr['comp15'])
    b2x = bucket_corrected(cs, pv, nm in NU, rr['comp15'])
    tab = tmir if kind == 'mir' else tmain
    idx = (MIR_NAMES if kind == 'mir' else MAIN_NAMES).index(nm)
    rs = []
    for bb in (15, 30, 60):
        v = tab[(tt, bb)][idx]
        rs.append(abs(v - lead - nxt / bb) * bb * bb)
    rmax = max(rs)
    passc = all(r <= b2c for r in rs)
    passx = all(r <= b2x for r in rs)
    okc = okc and passc
    okx = okx and passx
    print("  %-4s %-5s t=%s: resid(15/30/60) %7.4f %7.4f %7.4f"
          "  B2com %8.4f %s  B2corr %8.4f %s"
          % (kind, nm, tt, rs[0], rs[1], rs[2], b2c,
             "PASS" if passc else "FAIL", b2x,
             "PASS" if passx else "FAIL"), flush=True)
print("  DOMINATION committed-B2: %s ; corrected-B2: %s"
      % ("17/17 PASS" if okc else "FAIL", "17/17 PASS" if okx else "FAIL"),
      flush=True)

# ---------------- g_d adequacy accounting --------------------------
print("\n--- g_d = 0.02 adequacy per moment (zone floors, beta=15) ---",
      flush=True)
for (kind, lab, nm), rr in sorted(RESULTS.items()):
    if lab != 'zone' and not (kind == 'mir' and lab == 't2.9'):
        continue
    cs = rr['cs']
    pv = rr['pv']
    zs1 = 4 * BETA1 * pv
    lead = abs(cs[0])
    alloc = 0.02 * lead
    e1 = ((15 / 128) / zs1 ** 2 + 1.02 / zs1 ** 3) * BETA1 ** 2 * lead
    ctail = sum(abs(cs[j]) / BETA1 ** (j - 2) for j in range(4, len(cs)))
    print("  %s %s %-5s: g_d alloc %.4f | frozen-eps1 %.4f | c4+ tail %.4f"
          " | sum %.4f -> %s"
          % (kind, lab, nm, alloc, e1, ctail, e1 + ctail,
             "COVERED" if e1 + ctail <= alloc else "EXCEEDS g_d"),
          flush=True)

# ---------------- (g) M_sharp reproduction -------------------------
print("\n--- M_sharp reassembly reproduction ---", flush=True)
t_c = 2.9
b_c = 15.0
c_c = math.cos(t_c / 4)
s4_c = math.sin(t_c / 4)
d4_c = c_c - s4_c
SUP = math.exp(-4 * b_c * d4_c)
print("  c=%.6f s4=%.6f delta4=%.6f SUP=e^{-4*15*d4}=%.6e"
      % (c_c, s4_c, d4_c, SUP), flush=True)

ints_mirC = integrands(s4_c)
ints_mainC = integrands(c_c)


def val3(kind, nm, pv, beta, corrected=False):
    ints = ints_mirC if kind == 'mir' else ints_mainC
    poly, k0, fac, w, KERc = ints[(kind, nm)]
    ser = gauss_int_series(poly, pv)
    cf = conv(pv) * fac
    cs = []
    jj = 0
    while k0 + 2 * jj < NORD:
        cs.append(cf * ser.get(k0 + 2 * jj, 0.0))
        jj += 1
    comp = comp_fold(poly, k0, fac, pv, 15.0)
    if corrected:
        B2 = bucket_corrected(cs, pv, nm in NU, comp)
    else:
        B2 = bucket_committed(cs, cs[0], pv, nm in NU, comp)
    return abs(cs[0]) + abs(cs[1]) / beta + B2 / beta ** 2


def msharp(corrected=False, UD=None):
    muD_m = val3('mir', 'MD', s4_c, b_c, corrected) * SUP
    muF_m = val3('mir', 'MF', s4_c, b_c, corrected) * SUP
    nuD_m = val3('mir', 'MD2r', s4_c, b_c, corrected) * SUP / b_c ** 2
    nuF_m = val3('mir', 'MDFr', s4_c, b_c, corrected) * SUP / b_c ** 2
    muF_main = val3('main', 'muF', c_c, b_c, corrected) / b_c
    nuD_main = val3('main', 'nuD', c_c, b_c, corrected) / b_c ** 2
    nuF_main = val3('main', 'nuF', c_c, b_c, corrected) / b_c ** 3
    m_low = 1.79657
    if UD is None:
        UD = 2.3935 * 1.04 / (1 - math.exp(-15 * c_c * 0.72)
                              - 3 / (8 * 15 * c_c)) ** 2 \
            + 2 * 4.5 * SUP * 1.8 + 0.17
    M_cross = 4 * b_c ** 3 * (UD * nuF_m + muD_m * nuF_main
                              + muF_main * nuD_m
                              + muF_m * nuD_main) / m_low ** 2
    M_second = 4 * b_c ** 3 * (muD_m * nuF_m + muF_m * nuD_m) \
        / m_low ** 2
    return (muD_m, muF_m, nuD_m, nuF_m, muF_main, nuD_main, nuF_main,
            UD, M_cross, M_second, M_cross + M_second)


out = msharp(False)
print("  committed form: muD_m %.5g muF_m %.5g nuD_m %.5g nuF_m %.5g"
      % out[:4], flush=True)
print("                  muF_main %.5g nuD_main %.5g nuF_main %.5g"
      " U_D %.5g" % out[4:8], flush=True)
print("  M_sharp = %.5f [cross %.5f + second %.5f]  (transcript:"
      " 0.26831 [0.2665 + 0.0018052])" % (out[10], out[8], out[9]),
      flush=True)

# U_D piece analysis vs committed cascade1 bench truths
print("\n--- U_D piece analysis (cascade1 committed numbers) ---",
      flush=True)
T1 = 2.3935
br2 = 1 - math.exp(-15 * c_c * 0.72) - 3 / (8 * 15 * c_c)
main_piece = T1 * 1.04 / br2 ** 2
true_BK = 1.134 * (T1 / 2)     # bench slack mu1 = 1.134 (committed)
print("  U_D main piece = T1*1.04/br2^2 = %.4f ; committed bench truth"
      " 2*int_B K = 2*1.134*(T1/2) = %.4f -> main piece %s"
      % (main_piece, 2 * true_BK,
         "DOMINATES" if main_piece >= 2 * true_BK
         else "FAILS ITS TRUTH by x%.4f" % (2 * true_BK / main_piece)),
      flush=True)
mir_piece = 2 * 4.5 * SUP * 1.8
true_mir = 2 * (0.04788 / 2) / 2.15
rest_piece = 0.17
true_rest = 2 * (0.1671 / 2) / 187.0
UD_com = main_piece + mir_piece + rest_piece
true_2intK = 2 * true_BK + true_mir + true_rest
print("  mirror piece %.4f (truth ~%.4f) ; rest piece %.4f (truth"
      " ~%.5f)" % (mir_piece, true_mir, rest_piece, true_rest),
      flush=True)
print("  U_D total %.4f vs truth 2 int K ~ %.4f (x%.3f) vs true <D>"
      " = 2.5649 (bench)" % (UD_com, true_2intK, UD_com / true_2intK),
      flush=True)

outX = msharp(True)
print("\n  corrected-B2 M_sharp = %.5f [cross %.5f + second %.5f]"
      % (outX[10], outX[8], outX[9]), flush=True)
for UDv in (2.74, 3.0, 3.2):
    o = msharp(True, UD=UDv)
    print("  M_sharp with U_D=%.2f: %.5f" % (UDv, o[10]), flush=True)

json.dump({str(k): {kk: vv for kk, vv in v.items() if kk != 'cs'}
           | {'cs': v['cs']}
           for k, v in RESULTS.items()},
          open("stage2_results.json", "w"), indent=1)
print("\nstage 2 complete.", flush=True)
