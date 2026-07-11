"""CASCADE 3b - MAIN-SIDE LEADING EXTRACTIONS (fabrication desk):
mu_F, nu_D, nu_F at parameter c - the ink round's item (ii), sized
in v63 (the x81 nu_F crude chain is the dominant fat after the
mirror extraction; nu_F carries a strong next-order cancellation,
measured at (2.9,15): true -1.93e-4 vs leading -4.25e-4).

Judges: scripts/cascade3b_judges.py + committed transcript (read
from disk; incident #27).  Closed forms (C = 2c^2 - 1; B_nF as
CORRECTED in the judges' run-2 registration - the run-1 /8 was a
hand slip the judge's own Richardson exposed as x2 systematic):
  B_F  = -(2C+1) (sqrt(2pi)/4) c^{-7/2}     [beta-scaled mu_F]
  B_nD = (sqrt(2pi)/8) c^{-7/2}             [beta^2-scaled nu_D]
  B_nF = -(2C+1) (sqrt(2pi)/16) c^{-9/2}    [beta^3-scaled nu_F]

Engine: the audited pass-2 machinery VERBATIM at parameter c (the
same polynomials Ds, Fs the page used; no sympy.series).  Marks:
  N-A: gaussian parity;
  N-B: the three leadings equal the closed forms SYMBOLICALLY;
  N-C: the 1/beta coefficients within +-35% of the extrapolated
       drifts a_1 = 2 drift(30) - drift(15) (v63 instrument rule,
       adopted from the start);
  N-D: the nu_F cancellation quantified: at (2.9, 15) the two-term
       form lead + next/beta must land within 25% of the true
       quadrature value (committed in the 3b judges transcript at
       t=2.9, beta=15) - this is what buys the x2-class bucket.
Transcript exists when committed.
"""
import hashlib
import re
import sys

import mpmath as mp
import sympy as sp

mp.mp.dps = 30

print("=== CASCADE 3b: main-side leading extractions ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("sympy %s  mpmath %s  python %s"
      % (sp.__version__, mp.__version__, sys.version.split()[0]),
      flush=True)

sig, tau, c, eps = sp.symbols('sigma tau c epsilon', positive=True)
NORD = 10


def eps_deg(term):
    return term.as_powers_dict().get(eps, sp.Integer(0))


def trunc(expr, n=NORD):
    expr = sp.expand(expr)
    return sp.Add(*[t for t in expr.as_ordered_terms()
                    if eps_deg(t) < n])


def cos_taylor(v):
    return sp.Add(*[sp.Integer(-1)**k*(v*eps)**(2*k)/sp.factorial(2*k)
                    for k in range(0, 5)])


x = cos_taylor(sig)
y = cos_taylor(tau)
C = 2*c**2 - 1
Ds = trunc(x + y)
Ns = trunc(C*(2*x**2 - 1) + y*(C*x - 1 + x**2))
Fs = trunc(Ns - C*Ds)
P = trunc((1 - x)/2)
Q = trunc((1 - y)/2)
w_s = trunc(P + Q - P*Q/c**2)

rho2 = sig**2 + tau**2
W = sp.symbols('W')


def binom_series(alpha, order=6):
    e = sp.Add(*[sp.binomial(alpha, k)*(-W)**k
                 for k in range(0, order + 1)])
    return trunc(e.subs(W, w_s))


sqrt1mw = binom_series(sp.Rational(1, 2))
inv_sqrt1mw = binom_series(sp.Rational(-1, 2))
pow34 = binom_series(sp.Rational(-3, 4))
inv_1mw = binom_series(sp.Integer(-1))

expo = trunc(sp.expand((4*c/eps**2)*(sqrt1mw - 1)) + c*rho2/2)
assert sp.simplify(expo.subs(eps, 0)) == 0
wcorr = trunc(sp.Add(*[expo**k/sp.factorial(k) for k in range(0, 6)]))
invzs = eps**2/(4*c)
invz = trunc(invzs*inv_sqrt1mw)
KER = trunc(pow34*wcorr*(1 - sp.Rational(3, 8)*invz))


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
            return sp.sqrt(2*sp.pi/c)*sp.factorial2(k-1)/c**(k//2) \
                if k > 0 else sp.sqrt(2*sp.pi/c)
        total += coeff*m1(ks)*m1(ka)
    return sp.expand(total)


def kmoment(f):
    return gmoment(trunc(sp.expand(f)*KER))


r_weight = trunc(invzs*inv_sqrt1mw
                 - sp.Rational(3, 2)*invzs**2*inv_1mw)

print("=== MARKS N-A/N-B ===")
MF = kmoment(Fs)
MD2r = kmoment(sp.expand(Ds*Ds*r_weight))
MDFr = kmoment(sp.expand(Ds*Fs*r_weight))
for M, nm in [(MF, 'MF'), (MD2r, 'MD2r'), (MDFr, 'MDFr')]:
    for k in range(1, 8, 2):
        assert sp.simplify(M.coeff(eps, k)) == 0, \
            "parity fails: %s eps^%d" % (nm, k)
print("MARK N-A PASSES: gaussian parity.", flush=True)

CONV = 2/(sp.sqrt(2*sp.pi)*(4*c)**sp.Rational(3, 2))
targets = {
    'MF':   (-(2*C+1)*sp.sqrt(2*sp.pi)/4/c**sp.Rational(7, 2), 2, 1),
    'MD2r': (sp.sqrt(2*sp.pi)/8/c**sp.Rational(7, 2), 2,
             sp.Rational(1, 2)),
    'MDFr': (-(2*C+1)*sp.sqrt(2*sp.pi)/16/c**sp.Rational(9, 2), 4,
             sp.Rational(1, 2)),
}
leads = {}
nexts = {}
for M, nm in [(MF, 'MF'), (MD2r, 'MD2r'), (MDFr, 'MDFr')]:
    tgt, k0, fac = targets[nm]
    lead = sp.simplify(CONV*fac*M.coeff(eps, k0))
    nxt = sp.simplify(CONV*fac*M.coeff(eps, k0 + 2))
    leads[nm] = lead
    nexts[nm] = nxt
    diff = sp.simplify(lead - tgt)
    assert diff == 0, \
        "MARK N-B FAILS at %s: lead - target = %s" % (nm, diff)
    print("  %s: leading == closed form; next(1/beta) = %s"
          % (nm, sp.simplify(nxt)), flush=True)
print("MARK N-B PASSES.", flush=True)

print("=== MARK N-C: vs extrapolated drifts (3b judges transcript, "
      "bytes on disk) ===")
tab = {}
pat = re.compile(r"^\s+([\d.]+)\s+(\d+)\s\|\s*([+-][\d.]+)\s+"
                 r"([+-][\d.]+)\s+([+-][\d.]+)")
with open("cascade3b_judges_transcript.txt") as fh:
    for line in fh:
        m_ = pat.match(line)
        if m_:
            tab[(m_.group(1), int(m_.group(2)))] = \
                [mp.mpf(m_.group(i)) for i in (3, 4, 5)]
assert len(tab) == 9, "3b judges table incomplete: %d rows" % len(tab)
names = ['MF', 'MD2r', 'MDFr']
ok_all = True
for tt in ['0.5', '1.5', '2.9']:
    cv = mp.cos(mp.mpf(tt)/4)
    for i, nm in enumerate(names):
        lim = 2*tab[(tt, 60)][i] - tab[(tt, 30)][i]
        d15 = 15*(tab[(tt, 15)][i] - lim)
        d30 = 30*(tab[(tt, 30)][i] - lim)
        a1 = 2*d30 - d15
        pred = mp.mpf(sp.N(nexts[nm].subs(c, sp.Float(str(cv), 25)),
                           25).__str__())
        rel = abs(pred - a1)/max(abs(a1), mp.mpf('1e-12'))
        okc = rel < mp.mpf('0.35')
        ok_all = ok_all and okc
        print("  t=%s %s: a1 = %+.5f  extracted = %+.5f  rel %.3f %s"
              % (tt, nm, float(a1), float(pred), float(rel),
                 "OK" if okc else "OFF"), flush=True)
assert ok_all, "MARK N-C FAILS"
print("MARK N-C PASSES.", flush=True)

print("=== MARK N-D: the nu_F cancellation, two-term vs truth at "
      "(2.9, 15) ===")
cv = mp.cos(mp.mpf('2.9')/4)
true_nuF = tab[('2.9', 15)][2]   # beta^3-scaled, from the judge table
lead_v = mp.mpf(sp.N(leads['MDFr'].subs(c, sp.Float(str(cv), 25)),
                     25).__str__())
next_v = mp.mpf(sp.N(nexts['MDFr'].subs(c, sp.Float(str(cv), 25)),
                     25).__str__())
two_term = lead_v + next_v/15
rel = abs(two_term - true_nuF)/abs(true_nuF)
print("  beta^3 nu_F at (2.9,15): true %+.6f ; leading %+.6f ; "
      "lead+next/beta %+.6f ; rel %.3f"
      % (float(true_nuF), float(lead_v), float(two_term), float(rel)),
      flush=True)
ok_d = rel < mp.mpf('0.25')
print("MARK N-D %s: the two-term form %s the cancellation (the "
      "x2-class bucket is %s)." % ("PASSES" if ok_d else "FAILS",
      "captures" if ok_d else "misses",
      "buyable" if ok_d else "NOT yet buyable"), flush=True)
assert ok_d
print("\n3b EXTRACTION COMPLETE - the ink round's raw material is "
      "on the table: mirror leadings+nexts (v63), main-side "
      "leadings+nexts (this transcript), judges all matched.",
      flush=True)
