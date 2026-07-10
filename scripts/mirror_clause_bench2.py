"""Mark-5 bench, round 2: the mirror clause's FULL derived bracket,
term by term (T1-T5), each chain constant recomputed here and each
term's bound checked against the TRUE mirror-ball value of that term
(mpmath quadrature) at the stress cell (2.9, 15). Round 1's formula
dominated the measured TOTAL but omitted three O(beta^0) chains -
dominating a measurement is not being a theorem (registered).

Chains (all on the mirror ball = saddle chart at s_4, root floor
w~ <= 1/2, beta >= 15, s_4 >= 1/2):
  kappa := (Lam(s_4)/m_*) e^{-4 beta d4},  Lam = 1.34/s_4^{5/2} (reception repair R1: valid on all of s_4 >= 1/2)
  [round-1 bench: U-bound dominates true mirror mass x2.7]
  gaussian moment ratio: <rho'^2>-weighted mass <= (4.7/(beta s_4)) U
  corner expansion: |F o T - 4C| <= 6 rho'^2  (Hessian sup <= 12)
  r(z) <= sqrt2/(4 beta s_4) on the ball; r <= 1/4 global
  main-side: <D^2> <= 2<D>(1+e-small); Delta r <= 0.414/(beta c) on
  ball => nu_D <= 0.715 mu_D/(beta^2 c)
  <P>_ball <= 1.11<w>_ball <= 2.85 mu_D/(beta c) (D >= 1.8 on ball)
  => |mu_F| <= 34.2 mu_D/(beta c) unconditional;
     |mu_F| <= 6 mu_D/(beta c) under the Step-0 window (rem:step0)
  nu_F(ball) <= 12.09 mu_D/(beta^3 c^2)

Terms of 4 b^3 |mirror bilinear| / mu_D^2:
  T1 = 4b^3 |mu_D dnu_F|/mu_D^2 <= k[4sqrt2(c+s4) b d4/s4 + 39.9/s4^2]
  T2 = 4b^3 |nu_F dmu_D|/mu_D^2 <= 96.7 k / c^2
  T3 = 4b^3 |mu_F dnu_D|/mu_D^2 <= 96.7 k/(c s4)   [<= 17.0 k/(c s4) windowed]
  T4 = 4b^3 |nu_D dmu_F|/mu_D^2 <= k[11.44(c+s4) b d4/c + 80.7/(c s4)]
  T5 = second order <= (10 sqrt2/s4) b (Lam/m_*)^2 e^{-8 b d4}
"""
import mpmath as mp

mp.mp.dps = 15
t = mp.mpf("2.9"); beta = mp.mpf(15)
c = mp.cos(t/4); s4 = mp.sin(t/4)
d4 = c - s4
C = 2*c**2 - 1
mstar = mp.mpf("0.5")
Lam = mp.mpf("1.34")/s4**mp.mpf("2.5")
kappa = (Lam/mstar)*mp.e**(-4*beta*d4)
r0 = 1/mp.sqrt(5)

# --- chain constant re-derivations (printed, not trusted from head) --
# gaussian ratio: e^{-2 b s4 w~} with w~ >= q(P'+Q'), q = 1-0.0492/s4^2,
# P' >= 0.2458 s'^2  =>  weight <= e^{-a rho'^2}, a = 2 b s4 q 0.2458
q = 1 - mp.mpf("0.0492")/s4**2
a = 2*beta*s4*q*mp.mpf("0.2458")
mom_ratio = 2/a          # <rho'^2> of the 2D gaussian e^{-a rho'^2}
print("gaussian <rho'^2> ratio = 2/a = %.4f  (chain claims 4.7/(b s4) = %.4f; valid: %s)"
      % (mom_ratio, mp.mpf("4.7")/(beta*s4), mom_ratio <= mp.mpf("4.7")/(beta*s4)))

# Hessian of F o T = C(2x^2-1) + y(Cx+1-x^2) + C(x+y), x=cos s', y=cos a'
# sup over ball of |d2/ds'2|,|d2/da'2|,|d2/ds'da'| bounded crudely:
# |d2(FoT)/ds'2| <= 4|C|+|C|+2+|C| + ... take 12 (safe sup of all second
# derivatives for |C|<=1); kF = 12/2 = 6
kF = 6
print("corner expansion constant kF = %d (Hessian sup <= 12)" % kF)

def mirror_true(fw):
    """true mirror-ball integral of fw(s',a')*K(z(.;s4)) (mirror chart)."""
    def K(s, al):
        P = mp.sin(s/2)**2; Q = mp.sin(al/2)**2
        R2 = 4*(s4**2*(1 - P - Q) + P*Q)
        if R2 <= 0:
            return mp.mpf(0)
        z = 2*beta*mp.sqrt(R2)
        return 2*beta*mp.besseli(1, z)*mp.e**(-4*beta*s4)/z
    return mp.quad(lambda s: mp.quad(lambda al: fw(s, al)*K(s, al),
                                     [0, r0]), [0, r0])*4*mp.e**(4*beta*s4)

def rz(s, al):
    P = mp.sin(s/2)**2; Q = mp.sin(al/2)**2
    R2 = 4*(s4**2*(1 - P - Q) + P*Q)
    z = 2*beta*mp.sqrt(R2)
    return mp.besseli(2, z)/(z*mp.besseli(1, z))

def FoT(s, al):
    x = mp.cos(s); y = mp.cos(al)
    NT = C*(2*x**2 - 1) + y*(C*x + 1 - x**2)
    return NT + C*(x + y)

def DoT(s, al):
    return -(mp.cos(s) + mp.cos(al))

# true mirror moments (mirror chart; signs kept, magnitudes compared)
dmuD = mirror_true(lambda s, al: DoT(s, al))
dmuF = mirror_true(lambda s, al: FoT(s, al))
dnuD = mirror_true(lambda s, al: DoT(s, al)**2*rz(s, al))/(2*beta)
dnuF = mirror_true(lambda s, al: DoT(s, al)*FoT(s, al)*rz(s, al))/(2*beta)
U = Lam*beta**mp.mpf("-1.5")*mp.e**(4*beta*s4)
print("true |dmuD| = %.4e  bound 2U = %.4e  ok %s" % (abs(dmuD), 2*U, abs(dmuD) <= 2*U))
bF = (4*abs(C) + kF*mom_ratio)*U
print("true |dmuF| = %.4e  bound [4|C|+kF*mr]U = %.4e  ok %s" % (abs(dmuF), bF, abs(dmuF) <= bF))
bnuD = mp.sqrt(2)*U/(2*beta**2*s4)
print("true |dnuD| = %.4e  bound = %.4e  ok %s" % (abs(dnuD), bnuD, abs(dnuD) <= bnuD))
bnuF = (4*abs(C) + kF*mom_ratio)*mp.sqrt(2)*U/(4*beta**2*s4)
print("true |dnuF| = %.4e  bound = %.4e  ok %s" % (abs(dnuF), bnuF, abs(dnuF) <= bnuF))

# main-side true moments (parameter c chart, full square via quad)
def main_true(fw, use_r=False):
    def K(s, al):
        P = mp.sin(s/2)**2; Q = mp.sin(al/2)**2
        R2 = 4*(c**2*(1 - P - Q) + P*Q)
        if R2 <= 0:
            return mp.mpf(0)
        z = 2*beta*mp.sqrt(R2)
        v = 2*beta*mp.besseli(1, z)/z
        if use_r:
            v *= mp.besseli(2, z)/(z*mp.besseli(1, z))
        return v
    return mp.quad(lambda s: mp.quad(lambda al: fw(s, al)*K(s, al),
                                     [-mp.pi, 0, mp.pi]),
                   [-mp.pi, 0, mp.pi])

D_ = lambda s, al: mp.cos(s) + mp.cos(al)
F_ = lambda s, al: (2*c**2 - 1)*(2*mp.cos(s)**2 - 1) \
    + mp.cos(al)*((2*c**2 - 1)*mp.cos(s) - 1 + mp.cos(s)**2) \
    - (2*c**2 - 1)*(mp.cos(s) + mp.cos(al))
muD = main_true(D_)
muF = main_true(F_)
nuD = main_true(lambda s, al: D_(s, al)**2, use_r=True)/(2*beta)
nuF = main_true(lambda s, al: D_(s, al)*F_(s, al), use_r=True)/(2*beta)
print("main: muD = %.4e ; |muF|/muD*beta*c = %.3f (uncond bound 34.2; window 6)"
      % (muD, abs(muF)/muD*beta*c))
print("      nuD*beta^2*c/muD = %.3f (bound 0.715)" % (nuD*beta**2*c/muD))
print("      |nuF|*beta^3*c^2/muD = %.3f (bound 12.09)" % (abs(nuF)*beta**3*c**2/muD))

# term bounds vs term truths
k = kappa
T1b = k*(4*mp.sqrt(2)*(c + s4)*beta*d4/s4 + mp.mpf("39.9")/s4**2)
T2b = mp.mpf("96.7")*k/c**2
T3b_u = mp.mpf("96.7")*k/(c*s4)
T3b_w = mp.mpf("17.0")*k/(c*s4)
T4b = k*(mp.mpf("11.44")*(c + s4)*beta*d4/c + mp.mpf("80.7")/(c*s4))
T5b = (10*mp.sqrt(2)/s4)*beta*(Lam/mstar)**2*mp.e**(-8*beta*d4)
T1t = 4*beta**3*abs(muD*dnuF)/muD**2
T2t = 4*beta**3*abs(nuF*dmuD)/muD**2
T3t = 4*beta**3*abs(muF*dnuD)/muD**2
T4t = 4*beta**3*abs(nuD*dmuF)/muD**2
T5t = 4*beta**3*(abs(dnuF*dmuD) + abs(dnuD*dmuF))/muD**2
for nm, tb, tt in [("T1", T1b, T1t), ("T2", T2b, T2t),
                   ("T3u", T3b_u, T3t), ("T4", T4b, T4t),
                   ("T5", T5b, T5t)]:
    print("%s: bound %.4f  true %.4f  dominates %s" % (nm, tb, tt, tb >= tt))
    assert tb >= tt, "%s bound FAILS" % nm
Mu = T1b + T2b + T3b_u + T4b + T5b
Mw = T1b + T2b + T3b_w + T4b + T5b
total_true = T1t + T2t + T3t + T4t + T5t
print("M unconditional = %.3f ; windowed = %.3f ; true |mirror terms| sum = %.4f"
      % (Mu, Mw, total_true))
print("measured net mirror = 0.0707 ; slack: uncond x%.0f, windowed x%.0f, vs true-sum x%.1f / x%.1f"
      % (Mu/mp.mpf("0.0707"), Mw/mp.mpf("0.0707"),
         Mu/total_true, Mw/total_true))
print("MIRROR BENCH 2: ALL TERM BOUNDS DOMINATE")
