import sympy as sp

sig, tau, c, eps = sp.symbols('sigma tau c epsilon', positive=True)
NORD = 12

def eps_deg(term):
    return term.as_powers_dict().get(eps, sp.Integer(0))

def trunc(expr, n=NORD):
    expr = sp.expand(expr)
    return sp.Add(*[t for t in expr.as_ordered_terms() if eps_deg(t) < n])

def cos_taylor(v):
    return sp.Add(*[sp.Integer(-1)**k*(v*eps)**(2*k)/sp.factorial(2*k)
                    for k in range(0, 6)])

x = cos_taylor(sig); y = cos_taylor(tau)
C = 2*c**2 - 1
Ds = trunc(x + y)
Ns = trunc(C*(2*x**2 - 1) + y*(C*x - 1 + x**2))
Fs = trunc(Ns - C*Ds)
P = trunc((1 - x)/2); Q = trunc((1 - y)/2)
w_s = trunc(P + Q - P*Q/c**2)
rho2 = sig**2 + tau**2
W = sp.symbols('W')

def binom_series(alpha, order=7):
    e = sp.Add(*[sp.binomial(alpha, k)*(-W)**k for k in range(0, order + 1)])
    return trunc(e.subs(W, w_s))

print("building series...", flush=True)
sqrt1mw = binom_series(sp.Rational(1, 2))
inv_sqrt1mw = binom_series(sp.Rational(-1, 2))
pow34 = binom_series(sp.Rational(-3, 4))
inv_1mw = binom_series(sp.Integer(-1))

expo = trunc(sp.expand((4*c/eps**2)*(sqrt1mw - 1)) + c*rho2/2)
assert sp.simplify(expo.subs(eps, 0)) == 0
wcorr = trunc(sp.Add(*[expo**k/sp.factorial(k) for k in range(0, 7)]))
invzs = eps**2/(4*c)
invz = trunc(invzs*inv_sqrt1mw)
KER = trunc(pow34*wcorr*(1 - sp.Rational(3, 8)*invz
                         - sp.Rational(15, 128)*trunc(invz*invz)))
print("KER built", flush=True)

def gmoment(poly):
    poly = sp.expand(poly)
    total = 0
    for t in poly.as_ordered_terms():
        pd = t.as_powers_dict()
        ks = int(pd.get(sig, 0)); ka = int(pd.get(tau, 0))
        if ks % 2 or ka % 2:
            continue
        coeff = t/(sig**ks*tau**ka)
        def m1(k):
            return sp.sqrt(2*sp.pi/c)*sp.factorial2(k-1)/c**(k//2) \
                if k > 0 else sp.sqrt(2*sp.pi/c)
        total += coeff*m1(ks)*m1(ka)
    return sp.expand(total)

def kmoment(f):
    return gmoment(trunc(sp.expand(f)*KER))

def recip(series, n=NORD):
    d0 = series.subs(eps, 0)
    q = trunc(sp.expand(series/d0 - 1), n)
    out = sp.Integer(1); acc = sp.Integer(1)
    for _ in range(0, (n + 1)//2):
        acc = trunc(sp.expand(-q*acc), n)
        out = out + acc
    return trunc(sp.expand(out/d0), n)

mD = kmoment(Ds); print("mD done", flush=True)
mF = kmoment(Fs); print("mF done", flush=True)
mDF = kmoment(sp.expand(Ds*Fs)); print("mDF done", flush=True)
mD2 = kmoment(sp.expand(Ds*Ds)); print("mD2 done", flush=True)
Br1 = trunc(sp.expand(mD*mDF - mF*mD2))
r_zs = invzs - sp.Rational(3, 2)*invzs**2 + sp.Rational(3, 8)*invzs**3
num1 = sp.expand(2*r_zs*Br1/eps**6)
inv_mD2 = recip(trunc(sp.expand(mD*mD)))
ratio1 = trunc(sp.expand(num1*inv_mD2), 6)
T = (4*c**2 - 1)/(8*c**3)
print("X1 eps^0 diff:", sp.simplify(ratio1.coeff(eps, 0) - 2*T), flush=True)
print("r2_1 diff:", sp.simplify(ratio1.coeff(eps, 2)
      - (-44*c**4 + 29*c**2 - 6)/(32*c**6)), flush=True)
r3_1 = sp.simplify(ratio1.coeff(eps, 4))
print("r3_1(c) =", r3_1, flush=True)

dr = trunc(invzs*(inv_sqrt1mw - 1)
           - sp.Rational(3, 2)*invzs**2*(inv_1mw - 1)
           + sp.Rational(3, 8)*invzs**3*(binom_series(sp.Rational(-3, 2)) - 1))
mDFdr = kmoment(sp.expand(Ds*Fs*dr)); print("mDFdr done", flush=True)
mD2dr = kmoment(sp.expand(Ds*Ds*dr)); print("mD2dr done", flush=True)
Br2 = trunc(sp.expand(mD*mDFdr - mF*mD2dr))
num2 = sp.expand(2*Br2/eps**6)
ratio2 = trunc(sp.expand(num2*inv_mD2), 6)
print("X2 eps^0 diff:", sp.simplify(ratio2.coeff(eps, 0) + T), flush=True)
print("r2_2 diff:", sp.simplify(ratio2.coeff(eps, 2)
      - (18*c**4 - 7*c**2 + 1)/(16*c**6)), flush=True)
r3_2 = sp.simplify(ratio2.coeff(eps, 4))
print("r3_2(c) =", r3_2, flush=True)
r3 = sp.simplify(r3_1 + r3_2)
print("r3(c) =", r3, flush=True)
for cv in (0.99, 0.93, 0.87, 0.81, 0.7071):
    print("  c = %.4f : r3_1 = %+.4f  r3_2 = %+.4f  r3 = %+.4f"
          % (cv, float(r3_1.subs(c, cv)), float(r3_2.subs(c, cv)),
             float(r3.subs(c, cv))), flush=True)
print("R3 EXTRACTION COMPLETE", flush=True)
