"""CASCADE 4 - DESIGN PRE-SMOKE for the integral-remainder arc
(v83/v84; the arb smoke with contracts K1-K4 honored is the next
gate; THIS run is design-grade: mpmath high-precision numerical
differentiation of the TRUE quadrature moments in delta = 1/beta).

Questions answered (all at the stress cell t = 2.9):
 (P1) is v_m''(delta) empirically FINITE and stable on
      delta in [1/100, 1/15] for the two decisive mirror moments
      (MD: the mass carrier; MDFr: the nu_F carrier), with
      (1/2)|v''| <= B_m (the committed bucket constants)?  If yes,
      the S1 smoke has a real target; if the sup already breaches
      B_m at design grade, the integral route needs bigger buckets
      (still admissible: J2 only needs M_sharp in class).
 (P2) is Y''(delta) empirically finite with (1/2)|Y''| <=
      Theta_3(c) (the S2/(H_tail) budget form), where Y = X/delta
      and X = 4 beta^3 (mu_D nu_F - mu_F nu_D)/mu_D^2 at t = 2.9?
 (P3) does v''(delta) tend to a finite limit as delta -> 0
      (empirical support for the K2 C^2 extension)?

Method: v(delta) := judge-scaled moment at beta = 1/delta by
direct 2D quadrature of the TRUE integrand (same regions as the
committed judge scripts); second derivatives via mp.diff (central,
high precision) at sample deltas.  DESIGN ONLY - no certificate
claim; numbers exist when this transcript is committed.
"""
import hashlib
import sys
import time

import mpmath as mp

mp.mp.dps = 20

print("=== CASCADE 4 design pre-smoke (integral-remainder arc) ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("mpmath %s  python %s" % (mp.__version__,
                                sys.version.split()[0]), flush=True)

T_C = mp.mpf('2.9')
R = mp.mpf('1.2')

def core_factory(beta):
    t = T_C
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
        return (K_res, K_res*D, K_res*F, HB*D*D, HB*D*F)
    return core, c, s4

MX = ([mp.pi-R, mp.pi-R/2, mp.pi], [mp.pi-R, mp.pi-R/2, mp.pi])
REGS = [([0, R/2, R], [0, R/2, R]),
        ([mp.pi-R, mp.pi-R/2, mp.pi], [mp.pi-R, mp.pi-R/2, mp.pi]),
        ([R, 2, mp.pi], [0, R]), ([0, R], [R, 2, mp.pi]),
        ([R, 2, mp.pi-R], [R, 2, mp.pi-R]),
        ([mp.pi-R, mp.pi], [R, 2, mp.pi-R]),
        ([R, 2, mp.pi-R], [mp.pi-R, mp.pi])]

def q4(core, i, xs, ys):
    return 4*mp.quad(lambda s: mp.quad(
        lambda a: core(s, a)[i], ys), xs)

# FAST PATHS (the first launch computed all 35 region-quads per
# evaluation even for single-region carriers - killed at 2h05m
# with zero points; measured failure, transcript note): the mirror
# carriers integrate ONLY the mirror region (1 quad/eval); Y keeps
# the full set (35 quads/eval) and samples fewer deltas.
def vMD_of_delta(d):
    beta = 1/d
    core, c, s4 = core_factory(beta)
    return q4(core, 1, *MX)*mp.e**(4*beta*(c-s4))

def vNF_of_delta(d):
    beta = 1/d
    core, c, s4 = core_factory(beta)
    return q4(core, 4, *MX)*mp.e**(4*beta*(c-s4))*beta**2

def Y_of_delta(d):
    beta = 1/d
    core, c, s4 = core_factory(beta)
    tot = [mp.mpf(0)]*5
    for xs, ys in REGS:
        for i in range(5):
            tot[i] += q4(core, i, xs, ys)
    K1, KD, KF, HDD, HDF = tot
    X = 4*beta**3*(KD*HDF - KF*HDD)/KD**2
    return X/d

c = mp.cos(T_C/4)
r3 = (-12*c**6 - 485*c**4 + 796*c**2 - 224)/(1024*c**9)
Tc = (4*c**2-1)/(8*c**3)
Theta3 = abs(r3) + mp.mpf('1.10')*Tc/c**2 + mp.mpf('0.5')/c**3 \
    + mp.mpf('0.05')
print("stress cell t = 2.9: c = %s, Theta_3(c) = %s"
      % (mp.nstr(c, 6), mp.nstr(Theta3, 6)), flush=True)
print("committed B_m at s4(2.9) (diff-round transcripts): "
      "MD ~ 2.7, MDFr ~ 4.2 (per-cell values)", flush=True)

for nm, fn, budget, dlist in [
        ("v_MD(mirror)", vMD_of_delta, mp.mpf('2.7'),
         ['0.0666667', '0.05', '0.0333333', '0.02', '0.01']),
        ("v_nuF(mirror)", vNF_of_delta, mp.mpf('4.2'),
         ['0.0666667', '0.05', '0.0333333', '0.02', '0.01']),
        ("Y = X/delta", Y_of_delta, Theta3,
         ['0.0666667', '0.0333333', '0.02'])]:
    print("--- %s ---" % nm, flush=True)
    for dv in dlist:
        d0 = mp.mpf(dv)
        t0 = time.time()
        try:
            d2 = mp.diff(fn, d0, 2, method='step',
                         h=d0*mp.mpf('0.02'))
            half = abs(d2)/2
            ok = half <= budget
            print("  delta = %s (beta = %s): v'' = %s ; |v''|/2 = "
                  "%s vs budget %s : %s  (%.0fs)"
                  % (mp.nstr(d0, 4), mp.nstr(1/d0, 5),
                     mp.nstr(d2, 6), mp.nstr(half, 5),
                     mp.nstr(budget, 5),
                     "OK" if ok else "OVER", time.time()-t0),
                  flush=True)
        except Exception as e:
            print("  delta = %s : FAILED (%s)  (%.0fs)"
                  % (mp.nstr(d0, 4), e, time.time()-t0), flush=True)
print("\npre-smoke complete - design only; the arb smoke (S1/S2, "
      "contracts K1-K4) is the next gate.", flush=True)
