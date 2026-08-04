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
NORD = 18          # diff-audit sized repair: under the eps^-2
                   # clawback, exact MODEL orders reach only
                   # (NORD-4)/2 (at 14 that was c5 - the committed
                   # c6 was not the model's, audit instr3); at 18,
                   # c6/c7 are model-exact AND, decisively, ALL of
                   # the truncated polynomial's finitely many
                   # moment orders are extracted below (the plane
                   # moment is EXACTLY sum_{j<=Jmax} c_j^poly
                   # beta^-j): no polynomial order can be orphaned,
                   # and B2 claims MODEL coefficients only for
                   # c0/c1 (the judged leads/nexts)


def eps_deg(term):
    return term.as_powers_dict().get(eps, sp.Integer(0))


def trunc(expr, n=NORD):
    expr = sp.expand(expr)
    return sp.Add(*[t for t in expr.as_ordered_terms()
                    if eps_deg(t) < n])


def cos_taylor(v):
    return sp.Add(*[sp.Integer(-1)**k*(v*eps)**(2*k)/sp.factorial(2*k)
                    for k in range(0, 10)])


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
    for _ in range(10):
        wpow.append(trunc(sp.expand(wpow[-1]*w_s)))

    def binom_series(alpha, order=10):
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
    for k in range(1, 10):
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

    def kmi(f):
        """the truncated INTEGRAND polynomial (for the completion
        fold g_comp: its monomials x Gaussian tail moments)."""
        return trunc(sp.expand(f)*KER)

    # engine-derived <w> series (audit count 5 repair: w-bar is
    # EXTRACTED, never asserted): <w> = gmoment(w_s KER)/gmoment(KER)
    wm = gmoment(trunc(sp.expand(w_s)*KER))
    kn = gmoment(KER)
    w1 = sp.simplify(wm.coeff(eps, 2)/kn.coeff(eps, 0))
    w2 = sp.simplify(wm.coeff(eps, 4)/kn.coeff(eps, 0))
    return D_, F_, rw, km, kmi, (w1, w2)


CONV = 2/(sp.sqrt(2*sp.pi)*(4*p)**sp.Rational(3, 2))

def coeffs(M, k0, fac):
    """ALL available scaled orders c_0..c_J, J = (NORD-1-k0)//2
    (audit count 4 repair: the intra-truncation orders c4..cJ are
    part of the truncated moment and enter B2)."""
    J = (NORD - 1 - k0)//2
    return [sp.simplify(CONV*fac*M.coeff(eps, k0 + 2*j))
            for j in range(J + 1)]

print("extracting (NORD = %d, both charts)..." % NORD, flush=True)
Dm, Fm, rwm, kmm, kmim, WMIR = build(mirror=True)
MOM_MIR = {
    'MD':   (coeffs(kmm(Dm), 0, 1), kmim(Dm), 0, 1),
    'MF':   (coeffs(kmm(Fm), 0, 1), kmim(Fm), 0, 1),
    'MD2r': (coeffs(kmm(sp.expand(Dm*Dm*rwm)), 2, sp.Rational(1, 2)),
             kmim(sp.expand(Dm*Dm*rwm)), 2, sp.Rational(1, 2)),
    'MDFr': (coeffs(kmm(sp.expand(Dm*Fm*rwm)), 2, sp.Rational(1, 2)),
             kmim(sp.expand(Dm*Fm*rwm)), 2, sp.Rational(1, 2)),
}
Ds, Fs, rws, kms, kmis, WMAIN = build(mirror=False)
MOM_MAIN = {
    'muF':  (coeffs(kms(Fs), 2, 1), kmis(Fs), 2, 1),
    'nuD':  (coeffs(kms(sp.expand(Ds*Ds*rws)), 2, sp.Rational(1, 2)),
             kmis(sp.expand(Ds*Ds*rws)), 2, sp.Rational(1, 2)),
    'nuF':  (coeffs(kms(sp.expand(Ds*Fs*rws)), 4, sp.Rational(1, 2)),
             kmis(sp.expand(Ds*Fs*rws)), 4, sp.Rational(1, 2)),
}
print("extraction done; engine <w> leading (mirror chart): %s "
      "(the audit's exact 2/(4p beta): w1 = %s)"
      % (sp.simplify(WMIR[0]), sp.nsimplify(sp.simplify(WMIR[0]))),
      flush=True)

# consistency: leads/nexts must equal the judged v63/v67 forms
A_D = -2*sp.sqrt(2*sp.pi)/4/p**sp.Rational(5, 2)
assert sp.simplify(MOM_MIR['MD'][0][0] - A_D) == 0
B_nF = -(2*(2*p**2-1)+1)*sp.sqrt(2*sp.pi)/16/p**sp.Rational(9, 2)
assert sp.simplify(MOM_MAIN['nuF'][0][0] - B_nF) == 0
print("assert OK: leads reproduce the judged closed forms "
      "(spot: A_D, B_nF).", flush=True)

# ---------------- buckets ----------------
BETA1 = mp.mpf(15)
R1C = mp.mpf('1.2')*mp.sqrt(BETA1)     # completion radius in sigma

def comp_fold(intpoly, k0, fac, pv):
    """DERIVED completion fold, in bucket (beta^{-2}) units: the
    judge integrates the rectangle |s|,|alpha| <= 1.2, the chart
    moments integrate the plane; the difference is bounded monomial
    by monomial.  For each |a| sigma^i tau^j eps^k of the truncated
    integrand (k >= i+j STRUCTURALLY: sigma, tau only enter as
    sigma*eps, tau*eps - Codex link L3), the completion over the
    strip union {|sigma|>R} u {|tau|>R} (L2, an over-cover) is
      |a| beta^{-k/2} [2 T_i(R) Gbar_j + Gbar_i 2 T_j(R)],
    with T_k the Gaussian tail moments (recursion L1, upper) and
    Gbar_m = int |x|^m e^{-p x^2/2} dx (exact recursion).  The
    judge scaling multiplies by beta^{k0/2}; bucket units multiply
    by beta^2; the whole is beta-DECREASING for beta >= 15 (L4:
    worst log-derivative exponent 2 - k/2 + (i-1)/2 <= 1.5 by L3,
    and 1.5/15 = 0.1 < 0.72 p), so it is evaluated flat at
    BETA1."""
    # AUDIT COUNT 1-2 REPAIR: the docstring's old L3 (k >= i+j) is
    # FALSE - expo = (4p/eps^2)(sqrt(1-w)-1) + ... carries eps^-2,
    # exact counterexample sigma^4 eps^2 coeff -29/2400 at p=29/50
    # (internal cube audit; the Codex 4/4 endorsement rode the
    # prompt's false premise).  TRUE invariant: an expo monomial
    # has k = i+j-2, so a product of m expo factors gives k >=
    # i+j-2m (m <= 7 here).  Consequence: the per-monomial bucket
    # beta-exponent q = 2+(k0-k)/2+(max(i,j)-1)/2 can EXCEED
    # 0.72 p beta_1 (dust monomials, qmax ~ 6.5): each term is
    # multiplied by its exact sup-factor
    #   supfac(q) = max(1, (q/(a beta_1))^q e^{a beta_1 - q}),
    # a = 0.72 p, = sup_{beta>=beta_1} (beta/beta_1)^q
    # e^{-a(beta-beta_1)}; validity additionally needs the Mills
    # ratio T_i(R) p/(R^{i-1} e^{-p R^2/2}) nonincreasing in R -
    # design-checked below on an R-grid per order (assert).
    p_ = pv
    NT = 40
    def tails(R):
        T_ = [mp.e**(-p_*R**2/2)/(p_*R), mp.e**(-p_*R**2/2)/p_]
        for k in range(2, NT):
            T_.append(R**(k-1)*mp.e**(-p_*R**2/2)/p_
                      + (k-1)/p_*T_[k-2])
        return T_
    T = tails(R1C)
    # Mills-ratio monotonicity design check (orders that occur)
    Rg = [R1C*(1+mp.mpf(x)/4) for x in range(0, 9)]
    Tg = [tails(R) for R in Rg]
    for i_ in range(0, NT, 4):
        prev = None
        for R, T_ in zip(Rg, Tg):
            ratio = T_[i_]*p_/(R**max(i_-1, 0)
                               * mp.e**(-p_*R**2/2))
            assert prev is None or ratio <= prev*(1+mp.mpf('1e-20'))
            prev = ratio
    G = [mp.sqrt(2*mp.pi/p_), 2/p_]
    for m in range(2, NT):
        G.append((m-1)/p_*G[m-2])
    convn = 2/(mp.sqrt(2*mp.pi)*(4*pv)**mp.mpf('1.5'))
    a_rate = mp.mpf('0.72')*p_
    total = mp.mpf(0)
    for t_ in sp.expand(intpoly).as_ordered_terms():
        pd = t_.as_powers_dict()
        i = int(pd.get(sig, 0)); j = int(pd.get(tau, 0))
        k = int(pd.get(eps, 0))
        coeff = t_/(sig**i*tau**j*eps**k)
        a = abs(mp.mpf(sp.N(coeff.subs(p, sp.Float(str(pv), 25)),
                            25).__str__()))
        q = 2 + mp.mpf(k0-k)/2 + mp.mpf(max(i, j)-1)/2
        if q > a_rate*BETA1:
            supfac = (q/(a_rate*BETA1))**q*mp.e**(a_rate*BETA1-q)
        else:
            supfac = mp.mpf(1)
        total += a*BETA1**(mp.mpf(k0-k)/2) \
            * (2*T[i]*G[j] + G[i]*2*T[j])*supfac
    return convn*float(fac)*total*BETA1**2

def numv(expr, pv):
    return mp.mpf(sp.N(expr.subs(p, sp.Float(str(pv), 25)), 25)
                  .__str__())

def bucket(name, cj, wcoef, pv, nu_like, comp=mp.mpf(0)):
    """AUDIT-REPAIRED B2 at parameter value pv:
      B2 = |c2| + |c3|/beta_1 + sum_{j>=4}|c_j|/beta_1^{j-2}
           + MAG*(g_a + g_e1 [+ g_bc]) + MAG*g_d + comp,
    with MAG = sum_j |c_j|/beta_1^j the moment magnitude (count 3:
    relative sources convert via MAG, not |lead| alone); w-bar
    DERIVED from the engine's own <w> coefficients wcoef (count 5:
    the old 1.1 was asserted and measured-false; true leading
    2/(4 p beta)); g_e1 = the frozen-eps_1 source (count 3: the
    page's quotient cancellation does not apply per-moment):
    |eps_1(z_s)| <= (15/128)/z_s^2 + 1.02/z_s^3 relative;
    g_d = 0.02 covers ONLY the analytic-vs-polynomial Lagrange
    tails (at NORD=18: cos order-10, binomial order-11, exp
    order-10, riding eps^{20+} Gaussian moments - orders below
    1e-4 relative at beta_1); the POLYNOMIAL's own moment orders
    cannot be orphaned: the ctail sum below runs over ALL of them
    (the truncated polynomial's plane moment is a FINITE sum,
    diff-audit sized repair)."""
    cjv = [abs(numv(c, pv)) for c in cj]
    lead = cjv[0]
    MAG = sum(cjv[j]/BETA1**j for j in range(len(cjv)))
    c2 = cjv[2] if len(cjv) > 2 else mp.mpf(0)
    c3 = cjv[3] if len(cjv) > 3 else mp.mpf(0)
    ctail = sum(cjv[j]/BETA1**(j-2) for j in range(4, len(cjv)))
    zs1 = 4*BETA1*pv
    w1 = abs(numv(wcoef[0], pv)); w2 = abs(numv(wcoef[1], pv))
    wbar = (w1 + 2*w2/BETA1)/BETA1   # engine-derived; factor 2 on
                                     # the extracted next order as
                                     # its own tail guard
    g_a = (mp.mpf('4.94')/zs1**3 + mp.mpf('0.34')*wbar/zs1**2) \
        * BETA1**2
    g_e1 = (mp.mpf(15)/128/zs1**2 + mp.mpf('1.02')/zs1**3)*BETA1**2
    g_bc = mp.mpf(0)
    if nu_like:
        g_bc = (mp.mpf('1.23')/zs1**2
                + mp.mpf('1.37')*wbar/zs1**3 + mp.mpf('12.5')/zs1**4) \
            * BETA1**2
    g_d = mp.mpf('0.02')
    G = MAG*(g_a + g_e1 + g_bc + g_d)
    return c2 + c3/BETA1 + ctail + G + comp

Z_MIR = mp.mpf('0.5801')   # mirror zone floor (main-side buckets
                           # are checked per-cell at their own pv;
                           # the dead Z_MAIN removed - audit note)
BUCKETS = {}
for nm, (cj_, ip_, k0_, fac_) in MOM_MIR.items():
    BUCKETS[('mir', nm)] = bucket(nm, cj_, WMIR, Z_MIR,
                                  nm in ('MD2r', 'MDFr'),
                                  comp_fold(ip_, k0_, fac_, Z_MIR))
for nm, (cj_, ip_, k0_, fac_) in MOM_MAIN.items():
    BUCKETS[('main', nm)] = bucket(nm, cj_, WMAIN,
                                   mp.mpf('0.7071'),
                                   nm in ('nuD', 'nuF'),
                                   comp_fold(ip_, k0_, fac_,
                                             mp.mpf('0.7071')))
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
            cj_, ip_, k0_, fac_ = \
                (MOM_MIR if kind == 'mir' else MOM_MAIN)[nm]
            wc_ = WMIR if kind == 'mir' else WMAIN
            lead = numv(cj_[0], pv)
            nxt = numv(cj_[1], pv)
            B2 = bucket(nm, cj_, wc_, pv,
                        nm in ('MD2r', 'MDFr', 'nuD', 'nuF'),
                        comp_fold(ip_, k0_, fac_, pv))
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
    cj_, ip_, k0_, fac_ = \
        (MOM_MIR if kind == 'mir' else MOM_MAIN)[nm]
    wc_ = WMIR if kind == 'mir' else WMAIN
    lead = numv(cj_[0], pv)
    nxt = numv(cj_[1], pv)
    B2 = bucket(nm, cj_, wc_, pv,
                nm in ('MD2r', 'MDFr', 'nuD', 'nuF'),
                comp_fold(ip_, k0_, fac_, pv))
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
# AUDIT COUNT 5 REPAIR: U_D DERIVED (the old hand assembly sat
# BELOW its own committed bench truth 2 int_B K = 2.713).
# mu_D = <D> <= 2 int K (D <= 2, K >= 0); int K = ball + mirror +
# rest with the committed cascade-1 chains: ball = the GB machinery
# WITHOUT the (P+Q) weight (upper companion, absorption 1.089, rate
# floor 0.6811(P+Q), concavity 0.2214 s^2: int_B K_m <=
# 0.099736 (beta/c^{3/2}) 1.089 pi/(0.28651 beta c)); mirror = the
# zone-L MIRC (beta-free coefficient of cascade 2b) x SUP; rest =
# T5(2.9,15)/2 = 0.08355 from the committed cascade-1 design
# transcript (bytes cited; T5 bounds 2 int_rest K).  Fat ~x1.8 vs
# the bench 2.713+ but every factor has a witness.
U_ball = (BETA1/(4*mp.sqrt(2*mp.pi))/c_c**mp.mpf('1.5')) \
    * mp.mpf('1.089')*mp.pi \
    / (mp.mpf('0.2214')*mp.mpf('1.9')*mp.mpf('0.6811')*BETA1*c_c)
q4_c = (2*mp.sin(mp.mpf('0.6'))**2)/(4*s4_c**2)
U_mirc = (BETA1/(4*mp.sqrt(2*mp.pi))/s4_c**mp.mpf('1.5')) \
    * mp.mpf('1.230')*mp.pi \
    / (mp.mpf('0.2214')*mp.mpf('1.9')*(1-q4_c)*BETA1*s4_c)
U_D = 2*(U_ball + U_mirc*SUP + mp.mpf('0.08355'))
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
