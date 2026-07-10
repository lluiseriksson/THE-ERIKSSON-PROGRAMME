"""CASCADE 3 - THE JUDGES, PRE-REGISTERED (before the mirror page
exists; v41 rule applied to the mirror-chart extraction).

The mirror-chart extraction (repair item 3 of the mark-5 return,
acta v58) will extract, with the audited pass-2 machinery at
parameter s4, the LEADING COEFFICIENTS of the four mirror moments
over B' = the mirror rectangle (radius 6/5 at (pi,pi)):

  mu_D^mir  = int_{B'} K D          nu_D^mir = int_{B'} D^2 H_B
  mu_F^mir  = int_{B'} K F          nu_F^mir = int_{B'} D F H_B

CLOSED-FORM TARGETS (derived by hand at this desk from the mirror
chart z = z_s(s4) sqrt(1-w'), the exact Gaussian leading order, and
the center values D o T(0,0) = -2, F o T(0,0) = 4C; the SAME
sqrt(2pi)/4 constant of Cascade 1's T1; C = 1 - 2 s4^2):

  scaled mu_D^mir  := beta^{3/2} e^{-z_s(c)} e^{+4 beta delta4} mu_D^mir
                   -> A_D  = -2  * (sqrt(2pi)/4) s4^{-5/2}
  scaled mu_F^mir  ->  A_F  = +4C * (sqrt(2pi)/4) s4^{-5/2}
  beta^2-scaled nu_D^mir -> A_nD = +4  * (sqrt(2pi)/4) s4^{-7/2} / 8
                                 = (sqrt(2pi)/8) s4^{-7/2}
  beta^2-scaled nu_F^mir -> A_nF = -8C * (sqrt(2pi)/4) s4^{-7/2} / 8
                                 = -C (sqrt(2pi)/4) s4^{-7/2}

(the nu's carry H_B = r(z) K/(2 beta) and r(z_s(s4)) -> 1/(4 beta
s4): one factor beta^{-2} and the 1/(8 s4); hence the beta^2
scaling.)

ACCEPTANCE CONDITION for the extraction (registered NOW): the
symbolic leading coefficients must equal these four closed forms
IDENTICALLY in s4 (with C = 1 - 2 s4^2 substituted), and the
measured Richardson limits below are the CALIBRATION witnesses the
extraction must reproduce within the drift the 1/beta term allows.
Second condition: the extraction's 1/beta coefficients must land
within +-35% of the measured drifts (design tolerance; drifts are
differences of verified quadratures).

This script computes the quadrature tables at t in {2.2, 2.6, 2.9}
x beta in {15, 30, 60}, the Richardson limits, and compares to the
closed forms. It is the JUDGE: committed before the extraction
script exists. (Verified numerics; no load-bearing claim.)
"""
import hashlib
import sys
import time

import mpmath as mp

mp.mp.dps = 20

print("=== CASCADE 3 JUDGES: mirror-moment closed forms, "
      "pre-registered ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("mpmath %s  python %s" % (mp.__version__,
                                sys.version.split()[0]), flush=True)

R = mp.mpf('1.2')

def mirror_moments(tt, bb):
    """scaled (mu_D, mu_F, nu_D*beta^2, nu_F*beta^2) over B'."""
    t = mp.mpf(tt); beta = mp.mpf(bb)
    c = mp.cos(t/4); s4 = mp.sin(t/4)
    zs4 = 4*beta*s4
    def core(s, a):
        P = mp.sin(s/2)**2; Q = mp.sin(a/2)**2
        R2 = 4*c*c*(1-P)*(1-Q) + 4*s4*s4*P*Q
        z = 2*beta*mp.sqrt(R2)
        K_res = 2*beta**mp.mpf('2.5')*(mp.besseli(1, z)/mp.e**z/z) \
                * mp.e**(z-zs4)       # = K e^{-z_s(c)} e^{4 b d4} b^{3/2}
        rz = mp.besseli(2, z)/(z*mp.besseli(1, z))
        D = 2*(1-P-Q)
        CC = 2*c*c-1
        N = CC*mp.cos(2*s) + mp.cos(a)*(CC*mp.cos(s)-1+mp.cos(s)**2)
        F = N - CC*D
        HB_res = rz*K_res/(2*beta)    # H_B scaled likewise
        return (K_res*D, K_res*F, beta**2*HB_res*D*D,
                beta**2*HB_res*D*F)
    xs = [mp.pi-R, mp.pi-R/2, mp.pi]
    out = []
    for i in range(4):
        out.append(4*mp.quad(lambda s: mp.quad(
            lambda a: core(s, a)[i], xs), xs))
    return out

# N sanity: the N polynomial above must equal the moment-list form
# (design check of the integrand itself)
ok = True
for (ss, aa, cc) in [('1.1', '2.0', '0.83'), ('2.7', '0.4', '0.72')]:
    s = mp.mpf(ss); a = mp.mpf(aa); c = mp.mpf(cc)
    P = mp.sin(s/2)**2; Q = mp.sin(a/2)**2
    CC = 2*c*c-1
    N1 = CC*mp.cos(2*s) + mp.cos(a)*(CC*mp.cos(s)-1+mp.cos(s)**2)
    N2 = 2*CC - (10*CC+4)*P - 2*CC*Q + (8*CC+4)*P**2 \
        + (4*CC+8)*P*Q - 8*P**2*Q
    if abs(N1-N2) > mp.mpf(10)**-15:
        ok = False
print("[%s] N polynomial matches the v33 moment-list form"
      % ("PASS" if ok else "FAIL"), flush=True)

SQ2PI4 = mp.sqrt(2*mp.pi)/4
print("\n  t     beta |   muD_sc     muF_sc     nuD_sc*b^2  nuF_sc*b^2")
tables = {}
for tt in ['2.2', '2.6', '2.9']:
    for bb in [15, 30, 60]:
        t0 = time.time()
        vals = mirror_moments(tt, bb)
        tables[(tt, bb)] = vals
        print("  %s  %4d | %+.6f  %+.6f  %+.6f  %+.6f   (%.0fs)"
              % (tt, bb, *[float(v) for v in vals], time.time()-t0),
              flush=True)

print("\n--- Richardson limits (2 v(2b) - v(b)) vs closed forms ---")
print("  t    moment |  rich(15,30)  rich(30,60)   closed form")
names = ['muD', 'muF', 'nuD', 'nuF']
for tt in ['2.2', '2.6', '2.9']:
    t = mp.mpf(tt); s4 = mp.sin(t/4); C = 1-2*s4**2
    targets = [-2*SQ2PI4*s4**mp.mpf('-2.5'),
               4*C*SQ2PI4*s4**mp.mpf('-2.5'),
               (mp.sqrt(2*mp.pi)/8)*s4**mp.mpf('-3.5'),
               -C*SQ2PI4*s4**mp.mpf('-3.5')]
    for i in range(4):
        r1 = 2*tables[(tt, 30)][i] - tables[(tt, 15)][i]
        r2 = 2*tables[(tt, 60)][i] - tables[(tt, 30)][i]
        tg = targets[i]
        rel = abs(r2-tg)/abs(tg)
        print("  %s  %s   | %+.6f   %+.6f   %+.6f  rel %.3f %s"
              % (tt, names[i], float(r1), float(r2), float(tg),
                 float(rel), "OK" if rel < 0.02 else "OFF"),
              flush=True)
print("\nJUDGES REGISTERED: the extraction must produce these four "
      "closed forms symbolically (C = 1-2 s4^2), and its 1/beta "
      "coefficients must land within +-35% of the measured drifts "
      "v(beta) - limit above.", flush=True)
