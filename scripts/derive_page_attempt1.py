"""THE PAGE, symbolic assembly (exact by symbolic construction,
trust base sympy - the derive_holonomic precedent).

Object: X = mu_D nu_N - mu_N nu_D with mu_f = II K f,
nu_f = II D H_B f. Claim (mark 3 of the judge): the leading
coefficient of 4 beta^3 X / mu_D^2 equals T(c)/beta with
T(c) = (1/2 - 1/(8c^2))/c = (4c^2-1)/(8c^3), SYMBOLICALLY.

Method: Laplace substitution s = sig/sqrt(beta), a = tau/sqrt(beta);
every integrand becomes a series in 1/beta with polynomial-gaussian
coefficients; gaussian moments are exact; the bilinear form is
assembled and the 1/beta expansion read off. Kernel prefactors:
K ~ e^z z^(-3/2)(1 - 3/(8z)), H_B ~ e^z z^(-5/2)(1 - 15/(8z))
(from I_0 - 2 I_1/z with the two-term companions). Invariance
N -> F = N - CD used (X is invariant under N -> N - aD, a const).
The next symbolic coefficient r2(c) (the 1/beta^2 term) is also
printed - it is the saddle part of R_1(c) for the judge's band.
"""
import sympy as sp

s, a, c, B = sp.symbols('sigma tau c beta', positive=True)
ORD = 3  # keep through 1/beta^2 relative

x = sp.cos(s / sp.sqrt(B))
y = sp.cos(a / sp.sqrt(B))
P = (1 - x) / 2
Q = (1 - y) / 2
C = 2 * c**2 - 1
D = x + y
N = C * (2 * x**2 - 1) + y * (C * x - 1 + x**2)
F = sp.expand(N - C * D)

R2 = 4 * (c**2 * (1 - P - Q) + P * Q)
z = 2 * B * sp.sqrt(R2)
zs = 4 * B * c

# exponent difference and prefactors as 1/beta series (sigma,tau fixed)
expo = sp.series(z - zs, B, sp.oo, ORD).removeO()      # -(c/2)rho^2 + O(1/B)
invz = sp.series(1 / z, B, sp.oo, ORD + 1).removeO()
zfac32 = sp.series((zs / z)**sp.Rational(3, 2), B, sp.oo, ORD).removeO()
zfac52 = sp.series((zs / z)**sp.Rational(5, 2), B, sp.oo, ORD).removeO()

pref_K = zfac32 * (1 - sp.Rational(3, 8) * invz)
pref_H = zfac52 * (1 - sp.Rational(15, 8) * invz)

g = sp.exp(-c * (s**2 + a**2) / 2)   # the common gaussian
wcorr = sp.expand(sp.series(sp.exp(expo + c*(s**2+a**2)/2),
                            B, sp.oo, ORD).removeO())

def expand_poly(f):
    return sp.expand(sp.series(f, B, sp.oo, ORD).removeO())

Fp = expand_poly(F)
Dp = expand_poly(D)

def gmoment(poly):
    """integrate poly * g over the plane, term by term (exact)."""
    poly = sp.expand(poly)
    terms = poly.as_ordered_terms()
    total = 0
    for t in terms:
        coeff = t
        ks = sp.degree(t, s) if t.has(s) else 0
        ka = sp.degree(t, a) if t.has(a) else 0
        coeff = t / (s**ks * a**ka)
        if ks % 2 or ka % 2:
            continue
        def m1(k):
            # int x^k e^{-c x^2/2} dx = sqrt(2 pi/c) * (k-1)!! / c^(k/2)
            return sp.sqrt(2*sp.pi/c) * sp.factorial2(k-1) / c**(k//2) \
                   if k > 0 else sp.sqrt(2*sp.pi/c)
        total += coeff * m1(ks) * m1(ka)
    return sp.simplify(total)

def moment(f, measure):  # measure: 'K' or 'H'
    pref = pref_K if measure == 'K' else pref_H
    integrand = sp.expand(f * wcorr * expand_poly(pref))
    integrand = sp.expand(
        sp.series(integrand, B, sp.oo, ORD).removeO())
    return gmoment(integrand)

# mu-moments (measure K), with the 1/beta from ds da = dsig dtau / beta
muD = moment(Dp, 'K')
muF = moment(Fp, 'K')
# nu-moments: nu_f = II D H_B f; H_B/K ratio handled via separate
# prefactor; overall constants (e^{zs}, sqrt(2pi), zs powers) cancel
# in the ratio below EXCEPT the relative factor 1/(2 B z) between
# H_B and K/(2B): K = 2B e^z A, H_B = e^z/(sqrt(2pi) z^{5/2})(...)
# => H_B / K = (1/(2B)) * z^{-1} * [pref_H/pref_K adjustments], and
# we track pref_H, pref_K, invz explicitly:
nuD = moment(sp.expand(Dp * Dp * invz), 'H') / 2
nuF = moment(sp.expand(Dp * Fp * invz), 'H') / 2

X = sp.expand(muD * nuF - muF * nuD)
ratio = sp.simplify(4 * B**3 * X / muD**2)
ser = sp.series(ratio, B, sp.oo, 3)
print("4 b^3 X / mu_D^2 =", sp.simplify(ser))

lead = sp.simplify(ser.removeO().coeff(B, -1))
target = (4*c**2 - 1) / (8*c**3)
print("leading 1/beta coefficient:", sp.simplify(lead))
print("target T(c):", sp.simplify(target))
diff = sp.simplify(lead - target)
print("difference:", diff)
r2 = sp.simplify(ser.removeO().coeff(B, -2))
print("r2(c) [1/beta^2 saddle coefficient]:", r2)
print("r2 at judge cells c =", [round(float(r2.subs(c, cv)), 4)
      for cv in (0.99, 0.93, 0.87, 0.81)])
assert diff == 0, "MARK 3 FAILS: leading coefficient != T(c)"
print("MARK 3 PASSES: T(c) emerges symbolically.")
