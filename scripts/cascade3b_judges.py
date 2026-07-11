"""CASCADE 3b - MAIN-SIDE MOMENT JUDGES, PRE-REGISTERED (v41 rule;
the ink round's item (ii): nu_F, nu_D, mu_F leading extractions).

CLOSED-FORM TARGETS (hand-derived at this desk BEFORE the
extraction script exists; from the saddle chart at c, the exact
Gaussian leading order, F's quadratic form F = -(2C+1) s^2 + O(4)
(from lem:mini(b): F = -2C sin(3s/2)sin(s/2) - cos(alpha)
(2C sin^2(s/2) + sin^2 s)), D -> 2, r(z_s) -> 1/(4 beta c)):

  scaled mu_F  := beta^{5/2} e^{-z_s} <F>_K
              ->  B_F  = -(2C+1) (sqrt(2pi)/4) c^{-7/2}
  scaled nu_D  := beta^{7/2} e^{-z_s} nu_D   (nu_D = II D^2 H_B)
              ->  B_nD = (sqrt(2pi)/8) c^{-7/2}
  scaled nu_F  := beta^{9/2} e^{-z_s} nu_F   (nu_F = II D F H_B)
              ->  B_nF = -(2C+1) (sqrt(2pi)/16) c^{-9/2}
  (C = 2c^2 - 1.)

REGISTRATION CORRECTION (run 1, fail1 transcript preserved): this
desk first registered B_nF with sqrt(2pi)/8 - a hand-arithmetic
slip (the mirror A_nF pattern mis-transcribed); the run-1
Richardson limits measured EXACTLY HALF the registered form at all
three t's (rel 0.500 systematic, muF/nuD at rel 0.000), and the
re-derivation confirms /16:
  coeff(eps^4)<DFr> = D0 * F2 * r2 = 2 * (-(2C+1)) * 1/(4c)
  * gmoment(sigma^2) = -(2C+1) pi/c^3; times CONV/2 =
  -(2C+1) sqrt(2pi)/16 c^{-9/2}.
The QUADRATURE TABLES are the unmoved ground truth (identical in
both runs); only the closed-form line was wrong.  Consequence for
v63's note: the 'strong nu_F cancellation' was mostly this factor
2; the true next-order correction at (2.9,15) is ~9% (true
-1.932e-4 vs corrected leading -2.123e-4) - the x2-class bucket is
comfortably buyable.

ACCEPTANCE (registered NOW): (1) the extraction's leadings must
equal these closed forms SYMBOLICALLY; (2) its 1/beta coefficients
must land within +-35% of the extrapolated drifts
a_1 = 2 drift(30) - drift(15) from the tables below (the v60/v63
instrument rule, adopted from the start this time).

Tables: t in {0.5, 1.5, 2.9} x beta in {15, 30, 60} (bulk cells
first - the main side lives everywhere, unlike the mirror).
Verified numerics; no load-bearing claim.
"""
import hashlib
import sys
import time

import mpmath as mp

mp.mp.dps = 20

print("=== CASCADE 3b JUDGES: main-side closed forms, "
      "pre-registered ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("mpmath %s  python %s" % (mp.__version__,
                                sys.version.split()[0]), flush=True)

R = mp.mpf('1.2')

def main_moments(tt, bb):
    """beta-scaled (mu_F, nu_D beta^2, nu_F beta^3) m-units over the
    MAIN REGION = torus MINUS the mirror rectangle B'.

    RUN-3 CORRECTION (fail1 of the extraction, diagnosis at the
    coordinating desk): run 2 integrated the WHOLE torus; at t = 2.9
    the mirror block contributes beta A_F e^{-4 beta delta4} to the
    beta-scaled mu_F - +1.15 in drift(15), swamping the small main
    next-coefficient (extracted +0.29 vs whole-torus a1 -0.92; with
    the mirror term subtracted by hand they agree).  The extraction
    claims the MAIN-CHART moments; its judge must measure the main
    region - exactly complementary to the v63 mirror judges (B'
    only).  The mirror block's own expansion is v63's, already
    judged.  Closed forms and the +-35% band UNCHANGED."""
    t = mp.mpf(tt); beta = mp.mpf(bb)
    c = mp.cos(t/4); s4 = mp.sin(t/4); zs = 4*beta*c
    def core(s, a):
        P = mp.sin(s/2)**2; Q = mp.sin(a/2)**2
        R2 = 4*c*c*(1-P)*(1-Q) + 4*s4*s4*P*Q
        z = 2*beta*mp.sqrt(R2)
        K_res = 2*beta**mp.mpf('2.5')*(mp.besseli(1, z)/mp.e**z/z) \
                * mp.e**(z-zs)
        rz = mp.besseli(2, z)/(z*mp.besseli(1, z))
        D = 2*(1-P-Q)
        CC = 2*c*c-1
        N = CC*mp.cos(2*s) + mp.cos(a)*(CC*mp.cos(s)-1+mp.cos(s)**2)
        F = N - CC*D
        HB = rz*K_res/(2*beta)
        return (beta*K_res*F, beta**2*HB*D*D, beta**3*HB*D*F)
    regs = [([0, R/2, R], [0, R/2, R]),
            ([R, 2, mp.pi], [0, R]), ([0, R], [R, 2, mp.pi]),
            ([R, 2, mp.pi-R], [R, 2, mp.pi-R]),
            ([mp.pi-R, mp.pi], [R, 2, mp.pi-R]),
            ([R, 2, mp.pi-R], [mp.pi-R, mp.pi])]   # B' EXCLUDED
    out = [mp.mpf(0)]*3
    for xs, ys in regs:
        for i in range(3):
            out[i] += 4*mp.quad(lambda s: mp.quad(
                lambda a: core(s, a)[i], ys), xs)
    return out

SQ = mp.sqrt(2*mp.pi)
print("\n  t     beta |   muF_sc*b    nuD_sc*b^2   nuF_sc*b^3")
tables = {}
for tt in ['0.5', '1.5', '2.9']:
    for bb in [15, 30, 60]:
        t0 = time.time()
        vals = main_moments(tt, bb)
        tables[(tt, bb)] = vals
        print("  %s  %4d | %+.6f  %+.6f  %+.6f   (%.0fs)"
              % (tt, bb, *[float(v) for v in vals], time.time()-t0),
              flush=True)

print("\n--- Richardson limits vs closed forms ---")
print("  t    moment |  rich(15,30)  rich(30,60)   closed form")
names = ['muF', 'nuD', 'nuF']
for tt in ['0.5', '1.5', '2.9']:
    t = mp.mpf(tt); c = mp.cos(t/4); C = 2*c*c-1
    targets = [-(2*C+1)*(SQ/4)*c**mp.mpf('-3.5'),
               (SQ/8)*c**mp.mpf('-3.5'),
               -(2*C+1)*(SQ/16)*c**mp.mpf('-4.5')]
    for i in range(3):
        r1 = 2*tables[(tt, 30)][i] - tables[(tt, 15)][i]
        r2 = 2*tables[(tt, 60)][i] - tables[(tt, 30)][i]
        tg = targets[i]
        rel = abs(r2-tg)/abs(tg)
        print("  %s  %s   | %+.6f   %+.6f   %+.6f  rel %.3f %s"
              % (tt, names[i], float(r1), float(r2), float(tg),
                 float(rel), "OK" if rel < 0.03 else "OFF"),
              flush=True)
print("\nJUDGES REGISTERED: leadings symbolic; 1/beta coefficients "
      "within +-35% of a_1 = 2 drift(30) - drift(15).", flush=True)
