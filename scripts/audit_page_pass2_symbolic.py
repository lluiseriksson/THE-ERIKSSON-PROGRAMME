# audit_page_pass2_symbolic.py -- INDEPENDENT AUDIT DESK, STEP 3
# Adversarial spot-checks of scripts/derive_page_pass2.py (commit 2790d48,
# unchanged at HEAD cc55238). Written at the audit desk; the pipeline in
# CHECK 5 is an INDEPENDENT re-implementation at HIGHER truncation order
# (NORD=12 vs the fabricator's 10; cos Taylor one term deeper, binomial
# series one order deeper, exp Taylor one term deeper). If any truncated
# term contaminated the fabricator's extracted eps^0 / eps^2 coefficients,
# this rebuild produces DIFFERENT closed forms and the asserts fail.
#
# CHECK 1: gaussian-moment formula vs sympy.integrate (machinery).
# CHECK 2: trunc/eps_deg behavior + recip (geometric reciprocal) identity.
# CHECK 3: exact identity R^2 = 4c^2(1-w), w = P+Q-PQ/c^2 (symbolic).
# CHECK 4: Bessel facts (mpmath, dps=40): I_2 = I_0 - 2 I_1/z (DLMF
#          10.29.1); eta(z) z^3 -> 3/8 (so eta = O(z^-3) with known
#          constant, r two-term sufficient); kernel two-term
#          (1-w)^{-3/4} e^{z-z_s} (1-3/(8z)) vs exact I_1(z)/z reduced,
#          relative error ~ 15/(128 z^2) (the dropped eps_1 term is
#          O(eps^4)-relative -- see order ledger in the transcript).
# CHECK 5: independent higher-order symbolic rebuild: leading terms
#          == 2T(c) / -T(c) / T(c) and 1/beta coefficients == claimed
#          r2_1, r2_2, r2 closed forms; bracket N->F invariance; parity
#          and structural-zero asserts.
# CHECK 6: judge-cell values + mark-4 [residual, 3x] headroom numbers.

import time
import sympy as sp
import mpmath as mp

T0 = time.time()
FAILURES = []


def report(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    print("  [%s] %s %s" % (tag, name, detail))
    if not ok:
        FAILURES.append(name)


sig, tau, c, eps = sp.symbols('sigma tau c epsilon', positive=True)
NORD = 12          # fabricator used 10; two orders of headroom


def edeg(t):
    return t.as_powers_dict().get(eps, sp.Integer(0))


def cut(e, n=NORD):
    e = sp.expand(e)
    return sp.Add(*[t for t in e.as_ordered_terms() if edeg(t) < n])


# ----------------------------------------------------------------------
print("=== CHECK 1: gaussian moment formula vs sympy.integrate ===")


def gm1(k):
    return sp.sqrt(2*sp.pi/c)*sp.factorial2(k-1)/c**(k//2) \
        if k > 0 else sp.sqrt(2*sp.pi/c)


for k in (0, 2, 4, 6):
    direct = sp.integrate(sig**k*sp.exp(-c*sig**2/2), (sig, -sp.oo, sp.oo))
    ok = sp.simplify(direct - gm1(k)) == 0
    report("1D moment k=%d" % k, ok, "formula %s" % gm1(k))
odd = sp.integrate(sig**3*sp.exp(-c*sig**2/2), (sig, -sp.oo, sp.oo))
report("odd moment k=3 vanishes", sp.simplify(odd) == 0)
d2 = sp.integrate(sp.integrate(
    sig**2*tau**4*sp.exp(-c*(sig**2 + tau**2)/2),
    (sig, -sp.oo, sp.oo)), (tau, -sp.oo, sp.oo))
report("2D moment sigma^2 tau^4", sp.simplify(d2 - gm1(2)*gm1(4)) == 0,
       "= %s" % sp.simplify(gm1(2)*gm1(4)))

# ----------------------------------------------------------------------
print("=== CHECK 2: trunc/eps_deg behavior + geometric reciprocal ===")
ex = 3 + c*eps**2 + sig*eps**11 + eps**13/c
ct = cut(ex, 12)
report("cut drops >= eps^12, keeps eps^11",
       sp.expand(ct - (3 + c*eps**2 + sig*eps**11)) == 0, "-> %s" % ct)
report("eps_deg on pure number", edeg(sp.Integer(7)) == 0)
report("eps_deg on c*eps^4", edeg(c*eps**4) == 4)


def recip(series, n=NORD):
    # replicated logic of the fabricator's recip (geometric expansion)
    d0 = series.subs(eps, 0)
    q = cut(sp.expand(series/d0 - 1), n)
    out = sp.Integer(1)
    acc = sp.Integer(1)
    for _ in range(0, (n + 1)//2):
        acc = cut(sp.expand(-q*acc), n)
        out = out + acc
    return cut(sp.expand(out/d0), n)


S_test = 3 + 5*eps**2/c + c*eps**4 - eps**6
res = cut(sp.expand(recip(S_test, 10)*S_test - 1), 10)
report("recip identity (n=10): recip(S)*S = 1 + O(eps^10)",
       sp.expand(res) == 0, "residual below eps^10: %s" % res)
res12 = cut(sp.expand(recip(S_test, 12)*S_test - 1), 12)
report("recip identity (n=12)", sp.expand(res12) == 0)

# ----------------------------------------------------------------------
print("=== CHECK 3: exact deficit identity R^2 = 4c^2(1-w) ===")
Ps, Qs = sp.symbols('P Q')
R2sym = 4*(c**2*(1 - Ps - Qs) + Ps*Qs)
wsym = Ps + Qs - Ps*Qs/c**2
report("R^2 - 4c^2(1-w) == 0 symbolically",
       sp.simplify(R2sym - 4*c**2*(1 - wsym)) == 0)

# ----------------------------------------------------------------------
print("=== CHECK 4: Bessel facts (mpmath dps=40) ===")
mp.mp.dps = 40
for zv in (7.3, 30, 110):
    z = mp.mpf(zv)
    lhs = mp.besseli(2, z)
    rhs = mp.besseli(0, z) - 2*mp.besseli(1, z)/z
    rel = abs(lhs - rhs)/abs(lhs)
    report("I_2 = I_0 - 2 I_1/z at z=%s" % zv, rel < mp.mpf('1e-35'),
           "rel = %s" % mp.nstr(rel, 3))
# eta(z) z^3 -> 3/8 (next asymptotic coefficient of r(z))
vals = []
for zv in (500, 2000, 8000):
    z = mp.mpf(zv)
    r_ex = mp.besseli(2, z)/(z*mp.besseli(1, z))
    eta = r_ex - (1/z - 3/(2*z**2))
    vals.append(abs(eta)*z**3)
    print("    z=%6d : |eta| z^3 = %s" % (zv, mp.nstr(abs(eta)*z**3, 8)))
report("|eta| z^3 -> 3/8 = 0.375 (r_s two-term drop is O(eps^6))",
       abs(vals[-1] - mp.mpf(3)/8) < mp.mpf('0.001'))
# kernel two-term: reduced K vs (1-w)^{-3/4} e^{z-z_s}(1-3/(8z))
zs = mp.mpf(800)
w = mp.mpf('0.05')
z = zs*mp.sqrt(1 - w)
ker_true = (mp.besseli(1, z)/z)*mp.sqrt(2*mp.pi)*zs**mp.mpf(1.5)*mp.exp(-zs)
ker_model = (1 - w)**mp.mpf(-0.75)*mp.exp(z - zs)*(1 - 3/(8*z))
rel = abs(1 - ker_model/ker_true)
print("    z_s=800, w=0.05 : rel.err = %s ; rel*z^2 = %s (15/128 = %s)"
      % (mp.nstr(rel, 4), mp.nstr(rel*z**2, 5), mp.nstr(mp.mpf(15)/128, 5)))
report("kernel two-term error is ~15/(128 z^2), i.e. O(eps^4)-relative",
       abs(rel*z**2 - mp.mpf(15)/128) < mp.mpf('0.03'))
# H_B chain: H_B = r(z) K /(2 beta) -- pure algebra, shown symbolically
I0s, I1s, I2s, zsym, bsym = sp.symbols('I0 I1 I2 z beta', positive=True)
chain = (I2s/(zsym*I1s))*(2*bsym*I1s/zsym)/(2*bsym) - I2s/zsym**2
report("H_B = r(z) K/(2 beta) chain (algebraic identity)",
       sp.simplify(chain) == 0)

# ----------------------------------------------------------------------
print("=== CHECK 5: INDEPENDENT HIGHER-ORDER REBUILD (NORD=12) ===")
print("  building series (cos to (v eps)^10, binom to w^6, exp to k=6)...")


def my_cos(v):
    return sp.Add(*[sp.Integer(-1)**k*(v*eps)**(2*k)/sp.factorial(2*k)
                    for k in range(0, 6)])       # error O(eps^12)


x = my_cos(sig)
y = my_cos(tau)
Cc = 2*c**2 - 1
D = cut(x + y)
N = cut(Cc*(2*x**2 - 1) + y*(Cc*x - 1 + x**2))
F = cut(N - Cc*D)
report("F vanishes at the saddle (eps=0)", F.subs(eps, 0) == 0)
P = cut((1 - x)/2)
Q = cut((1 - y)/2)
w_s = cut(P + Q - P*Q/c**2)

# powers of w with truncation at each step
wpow = [sp.Integer(1), w_s]
for k in range(2, 7):
    wpow.append(cut(sp.expand(wpow[-1]*w_s)))


def one_minus_w_pow(a):
    return cut(sp.Add(*[sp.binomial(a, k)*sp.Integer(-1)**k*wpow[k]
                        for k in range(0, 7)]))


sqh = one_minus_w_pow(sp.Rational(1, 2))
ish = one_minus_w_pow(sp.Rational(-1, 2))
p34 = one_minus_w_pow(sp.Rational(-3, 4))
i1mw = one_minus_w_pow(sp.Integer(-1))

rho2 = sig**2 + tau**2
expo = cut(sp.expand((4*c/eps**2)*(sqh - 1)) + c*rho2/2)
report("gaussian exponent constant term vanishes",
       sp.simplify(expo.subs(eps, 0)) == 0)
# exp via truncated Taylor, powers cut stepwise (k=0..6)
wc = sp.Integer(1)
epow = sp.Integer(1)
for k in range(1, 7):
    epow = cut(sp.expand(epow*expo))
    wc = wc + epow/sp.factorial(k)
wc = cut(wc)
invzs = eps**2/(4*c)
invz = cut(sp.expand(invzs*ish))
KER = cut(sp.expand(cut(sp.expand(p34*wc))*(1 - sp.Rational(3, 8)*invz)))
print("  kernel built (%.0fs); computing moments..." % (time.time() - T0))


def gmom(poly):
    poly = sp.expand(poly)
    tot = 0
    for t in poly.as_ordered_terms():
        pd = t.as_powers_dict()
        ks = int(pd.get(sig, 0))
        ka = int(pd.get(tau, 0))
        if ks % 2 or ka % 2:
            continue
        tot += (t/(sig**ks*tau**ka))*gm1(ks)*gm1(ka)
    return sp.expand(tot)


def kmom(f):
    return gmom(cut(sp.expand(f)*KER))


mD = kmom(D)
mF = kmom(F)
mN = kmom(N)
mDF = kmom(cut(sp.expand(D*F)))
mDN = kmom(cut(sp.expand(D*N)))
mD2 = kmom(cut(sp.expand(D*D)))
print("  X_1 moments done (%.0fs)" % (time.time() - T0))

par_ok = True
for M, nm in ((mD, 'mD'), (mF, 'mF'), (mN, 'mN'), (mDF, 'mDF'),
              (mDN, 'mDN'), (mD2, 'mD2')):
    for k in range(1, NORD, 2):
        if sp.simplify(M.coeff(eps, k)) != 0:
            par_ok = False
            print("    parity violation: %s at eps^%d" % (nm, k))
report("gaussian parity (odd eps orders vanish, six moments)", par_ok)

BrN = cut(sp.expand(mD*mDN - mN*mD2))
BrF = cut(sp.expand(mD*mDF - mF*mD2))
report("bracket invariance N -> F = N - CD (exact)",
       sp.expand(BrN - BrF) == 0)
Br1 = BrF
report("Br1 eps^0 coefficient zero (structural)",
       sp.simplify(Br1.coeff(eps, 0)) == 0)
report("Br1 eps^2 coefficient zero (half-angle cancellation)",
       sp.simplify(Br1.coeff(eps, 2)) == 0)

rs2 = invzs - sp.Rational(3, 2)*invzs**2
num1 = sp.expand(2*rs2*Br1/eps**6)
imD2 = recip(cut(sp.expand(mD*mD)))
ratio1 = cut(sp.expand(num1*imD2), 6)
lead1 = sp.simplify(ratio1.coeff(eps, 0))
r21 = sp.simplify(ratio1.coeff(eps, 2))
Tc = (4*c**2 - 1)/(8*c**3)
report("beta X_1 leading == 2T(c)", sp.simplify(lead1 - 2*Tc) == 0,
       "lead = %s" % lead1)
r21_claim = (-44*c**4 + 29*c**2 - 6)/(32*c**6)
report("r2_1 == (-44c^4+29c^2-6)/(32c^6)",
       sp.simplify(r21 - r21_claim) == 0, "r2_1 = %s" % r21)

dr = cut(sp.expand(invzs*(ish - 1)
                   - sp.Rational(3, 2)*invzs**2*(i1mw - 1)))
mDFdr = kmom(cut(sp.expand(cut(sp.expand(D*F))*dr)))
mD2dr = kmom(cut(sp.expand(cut(sp.expand(D*D))*dr)))
print("  X_2 moments done (%.0fs)" % (time.time() - T0))
par2 = all(sp.simplify(M.coeff(eps, k)) == 0
           for M in (mDFdr, mD2dr) for k in range(1, NORD, 2))
report("gaussian parity (deficit moments)", par2)
Br2 = cut(sp.expand(mD*mDFdr - mF*mD2dr))
for k in (0, 2, 4):
    report("Br2 eps^%d coefficient zero" % k,
           sp.simplify(Br2.coeff(eps, k)) == 0)
num2 = sp.expand(2*Br2/eps**6)
ratio2 = cut(sp.expand(num2*imD2), 6)
lead2 = sp.simplify(ratio2.coeff(eps, 0))
r22 = sp.simplify(ratio2.coeff(eps, 2))
report("beta X_2 leading == -T(c)", sp.simplify(lead2 + Tc) == 0,
       "lead = %s" % lead2)
r22_claim = (18*c**4 - 7*c**2 + 1)/(16*c**6)
report("r2_2 == (18c^4-7c^2+1)/(16c^6)",
       sp.simplify(r22 - r22_claim) == 0, "r2_2 = %s" % r22)

r2tot = sp.simplify(r21 + r22)
r2_claim = (-8*c**4 + 15*c**2 - 4)/(32*c**6)
report("sum leading == T(c)", sp.simplify(lead1 + lead2 - Tc) == 0)
report("r2 == (-8c^4+15c^2-4)/(32c^6)",
       sp.simplify(r2tot - r2_claim) == 0, "r2 = %s" % r2tot)

# ----------------------------------------------------------------------
print("=== CHECK 6: judge cells + mark-4 headroom ===")
expected = {0.99: 0.1001, 0.93: 0.1444, 0.87: 0.1996, 0.81: 0.2653}
for cv, exp4 in expected.items():
    val = float(r2_claim.subs(c, cv))
    report("r2(%.2f) = %+.4f (fabricator printed %+.4f)"
           % (cv, val, exp4), abs(val - exp4) < 5e-5)
for cv, resid in ((0.99, 0.101), (0.81, 0.292)):
    val = float(r2_claim.subs(c, cv))
    lo, hi = resid, 3*resid
    win_lo, win_hi = lo - val, hi - val
    ok = win_hi > 0 and win_lo < win_hi
    report("mark-4 headroom at c=%.2f" % cv, ok,
           "band [%.4f, %.4f]; r2=%.4f; remainder window [%.4f, %.4f]"
           % (lo, hi, val, win_lo, win_hi))

# ----------------------------------------------------------------------
print("=" * 70)
if FAILURES:
    print("STEP 3 SYMBOLIC AUDIT: %d FAILURE(S): %s"
          % (len(FAILURES), FAILURES))
else:
    print("STEP 3 SYMBOLIC AUDIT: ALL CHECKS PASS (%.0fs total)"
          % (time.time() - T0))
