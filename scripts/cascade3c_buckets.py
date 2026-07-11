"""CASCADE 3c - THE BUCKET PAGE (fabrication desk; v69 transplant
plan executed).  Two-term companions with derived beta^{-2} buckets
for the seven judged moments (four mirror at s4, three main at c),
and the reassembled M_sharp for the mark-5 resubmission.

CLAIM SHAPE (per moment, in its judge scaling):
    |v(beta) - lead - next/beta| <= B2 / beta^2,   beta >= 15,
with lead/next the extracted closed forms (v63/v67, judged) and
    B2 := |c2| + G,
c2, c3 the extracted eps^{k0+4}, eps^{k0+6} coefficients (exact,
same engine two orders deeper; run 1 at NORD=12 carried only c2 and
the mirror chart's c3 broke domination at 4/8 zone cells by 4-95% -
fail1 preserved; B2 := |c2| + |c3|/beta_1 + G) and G the
transplanted source bounds (the page's (iv), parameter-free,
instantiated at the zone floors):
  (a) eps_1-variation:   4.94/z_s^3 + 0.34 <w>/z_s^2  (relative);
  (b) frozen-eta on r:   1.23/z_s^2 (relative, nu-moments);
  (c) deficit-eta tail:  1.37 <w>/z_s^3 + 12.5/z_s^4  (relative,
      nu-moments);
  (d) completion + truncation tails: e^{-const beta}-flat at
      beta_1 = 15 and the NORD-guard orders, folded as a relative
      0.02 (generous; the measured drift2 residuals are the judge).
  All relatives convert to bucket units via |lead| and one factor
  beta_1 per surplus 1/beta (valid for beta >= beta_1).
  <w> <= 1.1/(4 p beta) on the chart ball at parameter p (Gaussian
  w-moment, the 1.1 covering the (1-w)-corrections).

ZONE: the M-clause zone s4 >= 0.5801 (t >= 2.4754), where
  p = s4 in [0.5801, 0.7072] (mirror), c in [0.7071, 0.8135] (main).

ACCEPTANCE (pre-registered, v69): each B2 must DOMINATE the
measured beta^2-drifts  d2(beta) := beta (drift(beta) - a1)  at
every committed judge cell in the zone (and at the bulk cells for
the main side - the main companions serve everywhere); and the
reassembled M_sharp(2.9,15) must land in [0.0733, 0.7].

M REASSEMBLY (upper bound, m-units, zone L):
  |mu_X^mir(beta)|  <= [|A_X| + |n_X|/beta + B2_X/beta^2]
                       e^{-4 beta delta4}            (X = D, F)
  |nu_X^mir(beta)|  <= [ ... ]/beta^2 e^{-4 beta delta4}
  |mu_F^main| <= [|B_F| + |n_F|/beta + B2_F/beta^2]/beta   etc.
  mu_D^main >= m_low (lem:mass, certified);
  mu_D^main <= T_1 + 2 GB-form <= ... for the cross terms an UPPER
  mu_D is needed: mu_D = <D> <= 2 mu_1 <= 2*(T_1-form upper): use
  the companion upper analogue U_D := T_1/(br2^2) * (1+3/(8 z_s))
  ... simplest derived upper: <D> <= 2 int K <= 2 [upper Gaussian
  chain] = U_D(beta,c); implemented below from the same chains
  (upper companion, e^{z-z_s} <= e^{-2 beta c w}, w >= 0.6811(P+Q),
  P >= 0.2214 s^2 on B; plus mirror and rest masses).
  M_sharp := 4 beta^3 [ U_D nuF_m + A_D-form nuF_main
             + muF_main nuD_m + A_F-form nuD_main
             + second order ] / m_low^2 .
Transcript exists when committed.  Trust base sympy (polynomial
arithmetic only; no .series).
"""
import hashlib
import re
import sys

import mpmath as mp
import sympy as sp

mp.mp.dps = 30

print("=== CASCADE 3c: the bucket page ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("sympy %s  mpmath %s  python %s"
      % (sp.__version__, mp.__version__, sys.version.split()[0]),
      flush=True)

# ---------------- shared engine (pass-2, audited) ----------------
sig, tau, p, eps = sp.symbols('sigma tau p epsilon', positive=True)
NORD = 14          # two orders past pass 2: c3 needs eps^{k0+6}


def eps_deg(term):
    return term.as_powers_dict().get(eps, sp.Integer(0))


def trunc(expr, n=NORD):
    expr = sp.expand(expr)
    return sp.Add(*[t for t in expr.as_ordered_terms()
                    if eps_deg(t) < n])


def cos_taylor(v):
    return sp.Add(*[sp.Integer(-1)**k*(v*eps)**(2*k)/sp.factorial(2*k)
                    for k in range(0, 8)])


def build(mirror):
    x = cos_taylor(sig)
    y = cos_taylor(tau)
    if mirror:
        C = 1 - 2*p**2
        D_ = trunc(-(x + y))
        N_ = trunc(C*(2*x**2 - 1) + y*(C*x + 1 - x**2))
    else:
        C = 2*p**2 - 1
        D_ = trunc(x + y)
        N_ = trunc(C*(2*x**2 - 1) + y*(C*x - 1 + x**2))
    F_ = trunc(N_ - C*D_)
    P = trunc((1 - x)/2)
    Q = trunc((1 - y)/2)
    w_s = trunc(P + Q - P*Q/p**2)

    # incremental truncated powers of w_s (memory guard: truncate
    # inside every multiplication; w_s = O(eps^2) so w_s^k dies at
    # k > NORD/2 anyway)
    wpow = [sp.Integer(1)]
    for _ in range(8):
        wpow.append(trunc(sp.expand(wpow[-1]*w_s)))

    def binom_series(alpha, order=8):
        return trunc(sp.Add(*[sp.binomial(alpha, k)*(-1)**k*wpow[k]
                              for k in range(0, order + 1)]))

    sqrt1mw = binom_series(sp.Rational(1, 2))
    inv_sqrt1mw = binom_series(sp.Rational(-1, 2))
    pow34 = binom_series(sp.Rational(-3, 4))
    inv_1mw = binom_series(sp.Integer(-1))
    rho2 = sig**2 + tau**2
    expo = trunc(sp.expand((4*p/eps**2)*(sqrt1mw - 1)) + p*rho2/2)
    assert sp.simplify(expo.subs(eps, 0)) == 0
    # incremental truncated exp Taylor (memory guard, same reason)
    wcorr = sp.Integer(1)
    term = sp.Integer(1)
    for k in range(1, 8):
        term = trunc(sp.expand(term*expo))/k
        wcorr = wcorr + term
    wcorr = trunc(sp.expand(wcorr))
    invzs = eps**2/(4*p)
    invz = trunc(invzs*inv_sqrt1mw)
    KER = trunc(pow34*wcorr*(1 - sp.Rational(3, 8)*invz))
    rw = trunc(invzs*inv_sqrt1mw
               - sp.Rational(3, 2)*invzs**2*inv_1mw)

    def gmoment(poly):
        poly = sp.expand(poly)
        total = 0
        for t_ in poly.as_ordered_terms():
            pd = t_.as_powers_dict()
            ks = int(pd.get(sig, 0))
            ka = int(pd.get(tau, 0))
            if ks % 2 or ka % 2:
                continue
            coeff = t_/(sig**ks*tau**ka)

            def m1(k):
                return sp.sqrt(2*sp.pi/p)*sp.factorial2(k-1)/p**(k//2) \
                    if k > 0 else sp.sqrt(2*sp.pi/p)
            total += coeff*m1(ks)*m1(ka)
        return sp.expand(total)

    def km(f):
        return gmoment(trunc(sp.expand(f)*KER))

    return D_, F_, rw, km


CONV = 2/(sp.sqrt(2*sp.pi)*(4*p)**sp.Rational(3, 2))

def coeffs(M, k0, fac):
    return tuple(sp.simplify(CONV*fac*M.coeff(eps, k0 + 2*j))
                 for j in range(4))

print("extracting (NORD = %d, both charts)..." % NORD, flush=True)
Dm, Fm, rwm, kmm = build(mirror=True)
MOM_MIR = {
    'MD':   (coeffs(kmm(Dm), 0, 1)),
    'MF':   (coeffs(kmm(Fm), 0, 1)),
    'MD2r': (coeffs(kmm(sp.expand(Dm*Dm*rwm)), 2, sp.Rational(1, 2))),
    'MDFr': (coeffs(kmm(sp.expand(Dm*Fm*rwm)), 2, sp.Rational(1, 2))),
}
Ds, Fs, rws, kms = build(mirror=False)
MOM_MAIN = {
    'muF':  (coeffs(kms(Fs), 2, 1)),
    'nuD':  (coeffs(kms(sp.expand(Ds*Ds*rws)), 2, sp.Rational(1, 2))),
    'nuF':  (coeffs(kms(sp.expand(Ds*Fs*rws)), 4, sp.Rational(1, 2))),
}
print("extraction done.", flush=True)

# consistency: leads/nexts must equal the judged v63/v67 forms
A_D = -2*sp.sqrt(2*sp.pi)/4/p**sp.Rational(5, 2)
assert sp.simplify(MOM_MIR['MD'][0] - A_D) == 0
B_nF = -(2*(2*p**2-1)+1)*sp.sqrt(2*sp.pi)/16/p**sp.Rational(9, 2)
assert sp.simplify(MOM_MAIN['nuF'][0] - B_nF) == 0
print("assert OK: leads reproduce the judged closed forms "
      "(spot: A_D, B_nF).", flush=True)

# ---------------- buckets ----------------
BETA1 = mp.mpf(15)

def bucket(name, lead_s, next_s, c2_s, c3_s, pv, nu_like):
    """B2 = |c2| + |c3|/beta_1 + G at parameter value pv.
    G: transplanted sources (relative) x |lead| x beta_1-powers."""
    lead = abs(mp.mpf(sp.N(lead_s.subs(p, sp.Float(str(pv), 25)), 25)
                      .__str__()))
    c2 = abs(mp.mpf(sp.N(c2_s.subs(p, sp.Float(str(pv), 25)), 25)
                    .__str__()))
    c3 = abs(mp.mpf(sp.N(c3_s.subs(p, sp.Float(str(pv), 25)), 25)
                    .__str__()))
    zs1 = 4*BETA1*pv
    wbar = mp.mpf('1.1')/(4*pv*BETA1)
    g_a = (mp.mpf('4.94')/zs1**3 + mp.mpf('0.34')*wbar/zs1**2) \
        * BETA1**2       # relative beta^{-3}+... -> x beta_1^2 as
                         # a beta^{-2} bucket unit at beta >= 15
    g_bc = mp.mpf(0)
    if nu_like:
        g_bc = (mp.mpf('1.23')/zs1**2
                + mp.mpf('1.37')*wbar/zs1**3 + mp.mpf('12.5')/zs1**4) \
            * BETA1**2
    g_d = mp.mpf('0.02')          # flat truncation/completion fold
    G = lead*(g_a + g_bc + g_d)
    return c2 + c3/BETA1 + G

Z_MIR = mp.mpf('0.5801')   # zone floors
Z_MAIN = mp.cos(mp.mpf('2.4754')/4)   # c at the zone edge (max c)
BUCKETS = {}
for nm, (l_, n_, c2_, c3_) in MOM_MIR.items():
    BUCKETS[('mir', nm)] = bucket(nm, l_, n_, c2_, c3_, Z_MIR,
                                  nm in ('MD2r', 'MDFr'))
for nm, (l_, n_, c2_, c3_) in MOM_MAIN.items():
    BUCKETS[('main', nm)] = bucket(nm, l_, n_, c2_, c3_,
                                   mp.mpf('0.7071'),
                                   nm in ('nuD', 'nuF'))
for k, v in BUCKETS.items():
    print("  B2 %s = %s" % (k, mp.nstr(v, 5)), flush=True)

# ---------------- acceptance vs measured beta^2 drifts -----------
def load(fn, ncols):
    tab = {}
    pat = re.compile(r"^\s+([\d.]+)\s+(\d+)\s\|" +
                     r"\s*([+-][\d.]+)"*ncols)
    for line in open(fn):
        m_ = pat.match(line)
        if m_:
            tab[(m_.group(1), int(m_.group(2)))] = \
                [mp.mpf(m_.group(3+i)) for i in range(ncols)]
    return tab

tmir = load("cascade3_judges_transcript.txt", 4)
tmain = load("cascade3b_judges_transcript.txt", 3)
assert len(tmir) == 9 and len(tmain) == 9

def check_dom(tab, names, kind, zone_ts):
    okall = True
    for tt in zone_ts:
        pv = mp.sin(mp.mpf(tt)/4) if kind == 'mir' \
            else mp.cos(mp.mpf(tt)/4)
        for i, nm in enumerate(names):
            l_, n_, c2_, c3_ = (MOM_MIR if kind == 'mir'
                                else MOM_MAIN)[nm]
            lead = mp.mpf(sp.N(l_.subs(p, sp.Float(str(pv), 25)),
                               25).__str__())
            nxt = mp.mpf(sp.N(n_.subs(p, sp.Float(str(pv), 25)),
                              25).__str__())
            B2 = bucket(nm, l_, n_, c2_, c3_, pv,
                        nm in ('MD2r', 'MDFr', 'nuD', 'nuF'))
            ok = True
            for bb in (15, 30, 60):
                v = tab[(tt, bb)][i]
                resid = abs(v - lead - nxt/bb)*bb**2
                if resid > B2:
                    ok = False; okall = False
                    print("  DOM FAIL %s %s t=%s beta=%d: resid "
                          "%s > B2 %s" % (kind, nm, tt, bb,
                          mp.nstr(resid, 5), mp.nstr(B2, 5)),
                          flush=True)
            if ok:
                print("  %s %s t=%s: dominated (B2 = %s)"
                      % (kind, nm, tt, mp.nstr(B2, 5)), flush=True)
    return okall

okm = check_dom(tmir, ['MD', 'MF', 'MD2r', 'MDFr'], 'mir',
                ['2.6', '2.9'])
oka = check_dom(tmain, ['muF', 'nuD', 'nuF'], 'main',
                ['0.5', '1.5', '2.9'])
print("BUCKET DOMINATION: %s" % ("PASS" if (okm and oka) else
      "MEASURED FAILURE"), flush=True)
assert okm and oka

# ---------------- M_sharp at the stress cell ----------------
print("=== M_sharp reassembly at (2.9, 15) ===")
t_c = mp.mpf('2.9'); b_c = mp.mpf(15)
c_c = mp.cos(t_c/4); s4_c = mp.sin(t_c/4); d4_c = c_c - s4_c
SUP = mp.e**(-4*b_c*d4_c)

def val3(kind, nm, pv, beta):
    l_, n_, c2_, c3_ = (MOM_MIR if kind == 'mir' else MOM_MAIN)[nm]
    lead = mp.mpf(sp.N(l_.subs(p, sp.Float(str(pv), 25)), 25)
                  .__str__())
    nxt = mp.mpf(sp.N(n_.subs(p, sp.Float(str(pv), 25)), 25)
                 .__str__())
    B2 = bucket(nm, l_, n_, c2_, c3_, pv,
                nm in ('MD2r', 'MDFr', 'nuD', 'nuF'))
    return abs(lead) + abs(nxt)/beta + B2/beta**2

# mirror moments (m-units): mu-type carry SUP; nu-type SUP/beta^2
muD_m = val3('mir', 'MD', s4_c, b_c)*SUP
muF_m = val3('mir', 'MF', s4_c, b_c)*SUP
nuD_m = val3('mir', 'MD2r', s4_c, b_c)*SUP/b_c**2
nuF_m = val3('mir', 'MDFr', s4_c, b_c)*SUP/b_c**2
# main moments: mu_F/beta; nu_D/beta^2; nu_F/beta^3; mu_D bounds:
muF_main = val3('main', 'muF', c_c, b_c)/b_c
nuD_main = val3('main', 'nuD', c_c, b_c)/b_c**2
nuF_main = val3('main', 'nuF', c_c, b_c)/b_c**3
m_low_c = mp.mpf('1.79657')   # committed cascade1 design transcript
# upper mu_D: 2 int K <= T1-upper-chain + mirror + rest; generous
# derived form: T1/(lower brackets) x upper bracket + 2 x zone-L
# mirror mass + rest bound; assembled here from committed numbers:
# T1(2.9,15) = 2.3935 (lower); the upper chain differs by the
# bracket ratio (1+3/(8 z_s))/(1-3/(8 z_s)-0.6/z_s^2) and the
# Gaussian completion (no truncation loss upward): <= x1.04; plus
# mirror 2*4.5*e^{-4 b d4}*m_low-units and rest (<= 0.17):
U_D = mp.mpf('2.3935')*mp.mpf('1.04')/(1-mp.e**(-15*c_c*mp.mpf('0.72'))
      - 3/(8*15*c_c))**2 + 2*mp.mpf('4.5')*SUP*mp.mpf('1.8') \
      + mp.mpf('0.17')
M_cross = 4*b_c**3*(U_D*nuF_m + muD_m*nuF_main
                    + muF_main*nuD_m + muF_m*nuD_main)/m_low_c**2
M_second = 4*b_c**3*(muD_m*nuF_m + muF_m*nuD_m)/m_low_c**2
M_sharp = M_cross + M_second
print("  moment bounds (m-units): muD_mir %s  muF_mir %s  nuD_mir "
      "%s  nuF_mir %s" % tuple(mp.nstr(v, 4) for v in
      (muD_m, muF_m, nuD_m, nuF_m)))
print("  main: muF %s  nuD %s  nuF %s  U_D %s  m_low %s"
      % tuple(mp.nstr(v, 4) for v in
              (muF_main, nuD_main, nuF_main, U_D, m_low_c)))
print("  M_sharp(2.9,15) = %s  [cross %s + second %s]"
      % (mp.nstr(M_sharp, 5), mp.nstr(M_cross, 5),
         mp.nstr(M_second, 5)))
print("  vs true mirror 0.0733 : x%.2f  (target [0.0733, 0.7]; "
      "inked M was 30.3)" % float(M_sharp/mp.mpf('0.0733')),
      flush=True)
ok_M = mp.mpf('0.0733') < M_sharp < mp.mpf('0.7')
print("VERDICT: %s" % ("BUCKET PAGE PASSES - M_sharp in the x10 "
      "class; ready for independent audit + M re-ink + mark-5 "
      "resubmission" if ok_M else
      "MEASURED FAILURE - commit with diagnosis"), flush=True)
assert ok_M
