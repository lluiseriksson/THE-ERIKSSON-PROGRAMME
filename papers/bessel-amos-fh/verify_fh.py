import sympy as sp
from mpmath import mp, besseli, sqrt as msqrt, mpf

print("=== L1+L2+L4: symbolic algebra (independent) ===")
# L4: with a>0, beta>0, s=sqrt(a^2+beta^2), U=beta/(a+s): check 1/U - U == 2a/beta
a, beta = sp.symbols('a beta', positive=True)
s = sp.sqrt(a**2 + beta**2)
U = beta/(a+s)
expr = sp.simplify(1/U - U - 2*a/beta)
print("L4 identity 1/U - U - 2a/beta =", expr)

# L2 equivalence: rho_{nu+1} = 1/rho_nu - 2(nu+1)/beta  =>
# rho_nu - rho_{nu+1} <= 1/beta  <=>  1/rho_nu - rho_nu >= (2nu+1)/beta
r, nu = sp.symbols('rho nu', positive=True)
lhs = r - (1/r - 2*(nu+1)/beta)      # rho_nu - rho_{nu+1}
diff = sp.simplify((1/beta - lhs) - ((1/r - r) - (2*nu+1)/beta))
print("L2 equivalence residual =", diff)

print()
print("=== L1 numeric: (ln I_nu)'(beta) == rho_nu + nu/beta  (dps=50) ===")
mp.dps = 50
maxerr = mpf(0)
for b in [mpf('0.1'), mpf('0.5'), 2, 8, 32, 128, 500, 3000]:
    for n in range(1, 15):
        h = mpf(10)**-20
        lnd = (besseli(n, b+h) - besseli(n, b-h))/(2*h)/besseli(n, b)
        rho = besseli(n+1, b)/besseli(n, b)
        err = abs(lnd - (rho + n/b))
        maxerr = max(maxerr, err)
print("max |(ln I)' - (rho+nu/beta)| over grid:", maxerr)

print()
print("=== L3 numeric: Amos bound rho_nu < beta/(a+s), a=nu+1/2 ===")
worst = mpf('inf'); worst_at = None
import itertools
betas = [mpf('0.01'), mpf('0.1'), mpf('0.5'), 1, 2, 4, 8, 16, 32, 64, 128, 278, 512, 1000, 3365, 10000]
for b in betas:
    for n in list(range(0, 30)) + [50, 100, 500]:
        aa = mpf(n) + mpf('0.5')
        ss = msqrt(aa*aa + b*b)
        Ub = b/(aa+ss)
        rho = besseli(n+1, b)/besseli(n, b)
        margin = Ub - rho
        if margin < worst: worst, worst_at = margin, (float(b), n)
        if margin <= 0: print("VIOLATION at beta=%s nu=%s margin=%s" % (b, n, margin))
print("min margin U - rho over grid:", worst, "at (beta,nu)=", worst_at)

print()
print("=== FULL THEOREM direct check: rho_nu - rho_{nu+1} < 1/beta strictly ===")
worst2 = mpf('inf'); w2at=None
for b in betas:
    for n in range(1, 30):
        r1 = besseli(n+1, b)/besseli(n, b); r2 = besseli(n+2, b)/besseli(n+1, b)
        slack = 1/b - (r1 - r2)
        if slack < worst2: worst2, w2at = slack, (float(b), n)
        if slack <= 0: print("VIOLATION at", b, n)
print("min slack (1/beta - (rho_nu - rho_{nu+1})):", worst2, "at", w2at)

print()
print("=== COROLLARY: m(beta)=ln(I_1/I_2), m'(beta)<0 ===")
for b in [mpf('0.5'), 2, 8, 32, 128, 278]:
    h = mpf(10)**-15
    m  = lambda x: mp.log(besseli(1, x)/besseli(2, x))
    md = (m(b+h)-m(b-h))/(2*h)
    print("beta=%8s  m=%.6f  m'=%.3e" % (float(b), float(m(b)), float(md)))
