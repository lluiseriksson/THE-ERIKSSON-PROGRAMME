"""THE PAGE, pass 2 (symbolic assembly under the v46/v47/v48
directives; trust base sympy for the symbolic steps + mpmath for the
cell tests - the derive_holonomic precedent).

ORGANIZATION (v47, the single-measure resolution): everything lives
under the measure K. With r(z) := H_B z / I_1 = I_2/(z I_1) (the
exact measure ratio; H_B = I_2(z)/z^2, K = 2 beta I_1(z)/z),

  nu_f = II D f H_B = (1/(2 beta)) < D f r(z) >_K ,

and splitting r = r(z_s) + Delta r gives X = X_1 + X_2:

  beta X_1 = 2 beta^3 r(z_s) [<D><DF> - <F><D^2>] / <D>^2 -> 2T(c)
  beta X_2 = 2 beta^3 [<D><DF dr> - <F><D^2 dr>] / <D>^2  -> -T(c)

(F = N - CD; X_i invariant under N -> N - aD, so F replaces N; the
judges are the v47 pre-registered intermediate judges with
closed-form targets, and their sum is the exterior judge T(c) =
(4c^2-1)/(8c^3).)

DEFICIT VARIABLE (v45 repair plan / v46 lesson 3): the exact
polynomial deficit  w := P + Q - PQ/c^2  gives  z = z_s sqrt(1-w),
z_s = 4 beta c. All kernel prefactors are powers of (1-w) times
explicit 1/z_s corrections - no raw beta-series of sqrt(R2), which
is the zone that produced pass 1's c^144 blowup.

SERIES VARIABLE: eps = 1/sqrt(beta); s = sigma*eps, alpha = tau*eps.
NO sympy .series() anywhere (it fabricates spurious rational
functions of sigma, tau on these inputs - measured, twice): the only
transcendental step is cos -> explicit Taylor polynomial; everything
after is polynomial arithmetic with explicit truncation, and ratios
use the explicit geometric reciprocal. Gaussian weight e^{-c rho^2/2}
exact; wcorr = exp(z - z_s + c rho^2/2) via explicit truncated
Taylor (argument is O(eps^2)); its constant term vanishes
IDENTICALLY - first assert.

STEP A (cell-tested BEFORE any assembly - v46 lesson 2): the measure
ratio r(z) = 1/z - 3/(2z^2) + eta(z) is verified against exact
Bessel quotients at machine-range z; |eta| z^3 must be O(1) and the
two-term truncation must reproduce r to the advertised order.
Sources of the two-term forms: the v40 companions (I_1: 1 - 3/(8z),
|eps_1| <= 0.6/z^2; I_0: 1 + 1/(8z), |eps_0| <= 0.4/z^2) and the
exact identity I_2 = I_0 - 2 I_1 / z.

STEP B: X_1 extraction. Asserts: gaussian parity (odd eps orders
vanish), the leading bracket zero (the half-angle cancellation),
then leading coefficient == 2T(c) SYMBOLICALLY.

STEP C: X_2 extraction with the deficit weight
Delta r = (1/z_s)[(1-w)^{-1/2} - 1] - (3/(2 z_s^2))[(1-w)^{-1} - 1]
(+ eta-difference, remainder territory). Leading == -T(c)
SYMBOLICALLY.

STEP D: sum == T(c); the 1/beta coefficients r2_1, r2_2 printed and
evaluated at the judge cells (saddle part of R_1(c) for the
[residual, 3x] band, v41).
"""
import sympy as sp
import mpmath as mp

# ---------------------------------------------------------------
# STEP A - the measure-ratio substep, cell-tested first (v46 L2)
# ---------------------------------------------------------------
print("=== STEP A: measure ratio r(z) = I_2/(z I_1), cell test ===")
mp.mp.dps = 40
stepA_ok = True
for zv in [20, 30, 45, 60, 90, 112]:
    z = mp.mpf(zv)
    r_exact = mp.besseli(2, z)/(z*mp.besseli(1, z))
    r_two = 1/z - 3/(2*z**2)
    eta = r_exact - r_two
    scaled = abs(eta)*z**3
    print("  z = %4d : r = %.12f  two-term = %.12f  |eta| z^3 = %.4f"
          % (zv, float(r_exact), float(r_two), float(scaled)))
    # the eta z^3 scale must be O(1); design tolerance: bounded by 8
    stepA_ok = stepA_ok and (scaled < 8)
assert stepA_ok, "STEP A FAILS: eta scale not O(1/z^3)"
print("STEP A PASSES: two-term ratio verified, remainder O(1/z^3).")

# Delta r consistency at finite w (the deficit split used in X_2):
print("--- Delta r vs deficit form (z_s = 48, w in 0.05..0.3) ---")
for wv in [0.05, 0.15, 0.3]:
    zs = mp.mpf(48)
    w = mp.mpf(wv)
    z = zs*mp.sqrt(1-w)
    dr_exact = mp.besseli(2, z)/(z*mp.besseli(1, z)) \
        - mp.besseli(2, zs)/(zs*mp.besseli(1, zs))
    dr_two = (1/zs)*((1-w)**mp.mpf(-0.5) - 1) \
        - (3/(2*zs**2))*((1-w)**mp.mpf(-1) - 1)
    rel = abs(dr_exact - dr_two)/abs(dr_exact)
    print("  w = %.2f : dr = %.10f  two-term = %.10f  rel.err = %.2e"
          % (wv, float(dr_exact), float(dr_two), float(rel)))
    assert rel < 0.02, "STEP A2 FAILS: deficit form off at w=%s" % wv
print("STEP A2 PASSES: deficit split reproduces Delta r (<2% rel).")

# ---------------------------------------------------------------
# symbolic machinery - polynomial-only, explicit truncation
# ---------------------------------------------------------------
sig, tau, c, eps = sp.symbols('sigma tau c epsilon', positive=True)
NORD = 10          # keep eps^k for k < NORD (through eps^9)


def eps_deg(term):
    return term.as_powers_dict().get(eps, sp.Integer(0))


def trunc(expr, n=NORD):
    expr = sp.expand(expr)
    return sp.Add(*[t for t in expr.as_ordered_terms()
                    if eps_deg(t) < n])


def cos_taylor(v):
    # cos(v*eps): truncation error O(eps^10) - guard territory
    return sp.Add(*[sp.Integer(-1)**k*(v*eps)**(2*k)/sp.factorial(2*k)
                    for k in range(0, 5)])


x = cos_taylor(sig)
y = cos_taylor(tau)
C = 2*c**2 - 1
Ds = trunc(x + y)
Ns = trunc(C*(2*x**2 - 1) + y*(C*x - 1 + x**2))
Fs = trunc(Ns - C*Ds)            # vanishes at the saddle
P = trunc((1 - x)/2)
Q = trunc((1 - y)/2)
w_s = trunc(P + Q - P*Q/c**2)    # z = z_s sqrt(1-w), w = O(eps^2)

rho2 = sig**2 + tau**2
W = sp.symbols('W')


def binom_series(alpha, order=6):
    """(1-W)^alpha truncated at W^order, W -> w_s, truncated.
    w_s = O(eps^2) so W^6 = O(eps^12): guard."""
    e = sp.Add(*[sp.binomial(alpha, k)*(-W)**k
                 for k in range(0, order + 1)])
    return trunc(e.subs(W, w_s))


sqrt1mw = binom_series(sp.Rational(1, 2))
inv_sqrt1mw = binom_series(sp.Rational(-1, 2))
pow34 = binom_series(sp.Rational(-3, 4))
inv_1mw = binom_series(sp.Integer(-1))

# exponent: z - z_s + c rho^2/2, with z - z_s = (4c/eps^2)(sqrt(1-w)-1)
expo = trunc(sp.expand((4*c/eps**2)*(sqrt1mw - 1)) + c*rho2/2)
const_term = sp.simplify(expo.subs(eps, 0))
assert const_term == 0, \
    "PROVED-ZERO ASSERT FAILS: gaussian exponent constant term != 0"
print("assert OK: exponent constant term vanishes identically "
      "(the gaussian is exact at leading order).")
# exp via explicit truncated Taylor (expo = O(eps^2): k=5 is guard)
wcorr = trunc(sp.Add(*[expo**k/sp.factorial(k) for k in range(0, 6)]))

invzs = eps**2/(4*c)
invz = trunc(invzs*inv_sqrt1mw)
KER = trunc(pow34*wcorr*(1 - sp.Rational(3, 8)*invz))


def gmoment(poly):
    """II poly e^{-c rho^2/2} dsig dtau, exact, term by term."""
    poly = sp.expand(poly)
    total = 0
    for t in poly.as_ordered_terms():
        pd = t.as_powers_dict()
        ks = int(pd.get(sig, 0))
        ka = int(pd.get(tau, 0))
        if ks % 2 or ka % 2:
            continue
        coeff = t/(sig**ks*tau**ka)

        def m1(k):
            return sp.sqrt(2*sp.pi/c)*sp.factorial2(k-1)/c**(k//2) \
                if k > 0 else sp.sqrt(2*sp.pi/c)
        total += coeff*m1(ks)*m1(ka)
    return sp.expand(total)


def kmoment(f):
    """<f>_K / (common constant 2 beta e^{z_s} (1)/(sqrt(2pi)
    z_s^{3/2} beta)): moment against the reduced kernel KER in the
    saddle chart. The common constant cancels in every ratio below."""
    return gmoment(trunc(sp.expand(f)*KER))


def recip(series, n=NORD):
    """1/series for series with nonzero constant eps-term, explicit
    geometric expansion (no sympy series)."""
    d0 = series.subs(eps, 0)
    q = trunc(sp.expand(series/d0 - 1), n)   # O(eps^2)
    out = sp.Integer(1)
    acc = sp.Integer(1)
    for _ in range(0, (n + 1)//2):
        acc = trunc(sp.expand(-q*acc), n)
        out = out + acc
    return trunc(sp.expand(out/d0), n)


print("=== STEP B: X_1 (frozen ratio) against judge 2T(c) ===")
mD = kmoment(Ds)
mF = kmoment(Fs)
mDF = kmoment(sp.expand(Ds*Fs))
mD2 = kmoment(sp.expand(Ds*Ds))

for M, nm in [(mD, 'mD'), (mF, 'mF'), (mDF, 'mDF'), (mD2, 'mD2')]:
    for k in range(1, 8, 2):
        assert sp.simplify(M.coeff(eps, k)) == 0, \
            "parity assert fails: %s at eps^%d" % (nm, k)
print("assert OK: gaussian parity (odd orders vanish) in all four "
      "moments.")

Br1 = trunc(sp.expand(mD*mDF - mF*mD2))
lead2 = sp.simplify(Br1.coeff(eps, 2))
assert lead2 == 0, "HALF-ANGLE ZERO FAILS: bracket eps^2 term = %s" \
    % lead2
print("assert OK: bracket leading (eps^2) term vanishes - the "
      "half-angle cancellation, symbolically.")

# r(z_s) two-term (companions v40 + I_2 = I_0 - 2 I_1/z):
r_zs = invzs - sp.Rational(3, 2)*invzs**2
# beta X_1 = 2 beta^3 r(z_s) Br1 / mD^2 ; beta^3 = eps^{-6}
num1 = sp.expand(2*r_zs*Br1/eps**6)
inv_mD2 = recip(trunc(sp.expand(mD*mD)))
ratio1 = trunc(sp.expand(num1*inv_mD2), 4)
lead1 = sp.simplify(ratio1.coeff(eps, 0))
T = (4*c**2 - 1)/(8*c**3)
diff1 = sp.simplify(lead1 - 2*T)
print("beta X_1 leading coefficient:", sp.simplify(lead1))
print("target 2T(c) =", sp.simplify(2*T))
assert diff1 == 0, "X_1 EXTRACTION FAILS: leading != 2T(c), diff=%s" \
    % diff1
print("STEP B PASSES: beta X_1 -> 2T(c) SYMBOLICALLY.")
r2_1 = sp.simplify(ratio1.coeff(eps, 2))
print("r2_1(c) [1/beta coefficient of beta X_1]:", r2_1)

print("=== STEP C: X_2 (deficit weight) against judge -T(c) ===")
dr = trunc(invzs*(inv_sqrt1mw - 1)
           - sp.Rational(3, 2)*invzs**2*(inv_1mw - 1))
mDFdr = kmoment(sp.expand(Ds*Fs*dr))
mD2dr = kmoment(sp.expand(Ds*Ds*dr))
for M, nm in [(mDFdr, 'mDFdr'), (mD2dr, 'mD2dr')]:
    for k in range(1, 8, 2):
        assert sp.simplify(M.coeff(eps, k)) == 0, \
            "parity assert fails: %s at eps^%d" % (nm, k)
Br2 = trunc(sp.expand(mD*mDFdr - mF*mD2dr))
lead4 = sp.simplify(Br2.coeff(eps, 4))
assert lead4 == 0, "X_2 bracket eps^4 term nonzero: %s" % lead4
print("assert OK: X_2 bracket eps^4 term vanishes.")
num2 = sp.expand(2*Br2/eps**6)
ratio2 = trunc(sp.expand(num2*inv_mD2), 4)
lead2c = sp.simplify(ratio2.coeff(eps, 0))
diff2 = sp.simplify(lead2c + T)
print("beta X_2 leading coefficient:", sp.simplify(lead2c))
print("target -T(c) =", sp.simplify(-T))
assert diff2 == 0, "X_2 EXTRACTION FAILS: leading != -T(c), diff=%s" \
    % diff2
print("STEP C PASSES: beta X_2 -> -T(c) SYMBOLICALLY.")
r2_2 = sp.simplify(ratio2.coeff(eps, 2))
print("r2_2(c) [1/beta coefficient of beta X_2]:", r2_2)

print("=== STEP D: sum against the exterior judge ===")
total_lead = sp.simplify(lead1 + lead2c)
assert sp.simplify(total_lead - T) == 0, "SUM FAILS vs exterior judge"
print("SUM PASSES: beta(X_1 + X_2) -> T(c) = (4c^2-1)/(8c^3) "
      "SYMBOLICALLY.")
r2 = sp.simplify(r2_1 + r2_2)
print("r2(c) [saddle part of R_1(c)]:", r2)
print("judge-cell evaluation (v41 band: residuals 0.101-0.292, "
      "R_1 in [residual, 3x]):")
for cv in (0.99, 0.93, 0.87, 0.81):
    print("  c = %.2f : r2_1 = %+.4f  r2_2 = %+.4f  r2 = %+.4f"
          % (cv, float(r2_1.subs(c, cv)), float(r2_2.subs(c, cv)),
             float(r2.subs(c, cv))))
print("PASS 2 COMPLETE: all symbolic marks passed; r2(c) awaits the "
      "auditor's band check.")
