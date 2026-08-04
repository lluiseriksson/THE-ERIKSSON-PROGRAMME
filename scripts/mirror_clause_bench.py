"""Mark-5 bench: the mirror clause's derived constants, checked
against truth at the pre-registered stress cell (t,beta) = (2.9,15)
BEFORE ink (bench calibrates, derived constants go to ink - ghost
#23 rule).

The template (Zone I, s_4 = sin(t/4) >= 1/2):
  M_I = (Lam(s_4)/m_*) [4(c+s_4)(1/s_4+1/c) * (beta d4) + Th_m]
        * e^{-4 beta d4}
      + (10 sqrt2/s_4)(Lam/m_*)^2 * beta * e^{-8 beta d4},
  d4 = c - s_4 = sqrt2 sin((pi-t)/4)   [exact, half-angle],
  Lam(s_4) = 1.21/s_4^{5/2}  [derived: K <= 2 beta e^z/(sqrt(2pi)
    z^{3/2}) for z >= 20 (companions upper); z >= z_s(s_4)/sqrt2 on
    the ball (root floor); e^z <= e^{z_s} e^{-2 beta s_4 w~};
    w~ >= (1 - 0.0492/s_4^2)(P'+Q') on |s'|,|a'| <= 1/sqrt5;
    P' >= 0.2458 s'^2],
  Th_m = 12 sqrt2/(c s_4)  [the mu_F delta-nu_D bundle via the
    Step-0 window |E-C| <= 6/(beta c)].

Checks:
 1. P' floor and w~ floor hold pointwise on the ball (sampled).
 2. U-bound = Lam(s_4) beta^{-3/2} e^{4 beta s_4} dominates the TRUE
    mirror-ball mass integral (numerical, mpmath).
 3. M_I(2.9,15) dominates the measured stress-cell mirror
    contribution |−0.0707| with slack in the x10 class (< x100).
 4. C = (c-s_4)(c+s_4) identity and sup x e^{-4x} = 1/(4e).
"""
import mpmath as mp

mp.mp.dps = 25

t = mp.mpf("2.9")
beta = mp.mpf(15)
c = mp.cos(t/4)
s4 = mp.sin(t/4)
d4 = mp.sqrt(2)*mp.sin((mp.pi - t)/4)

# check 4a: half-angle identity
assert abs((c - s4) - d4) < mp.mpf(10)**-20, "d4 identity fails"
C = 2*c**2 - 1
assert abs(C - (c - s4)*(c + s4)) < mp.mpf(10)**-20, "C identity fails"
print("check 4: C = (c-s4)(c+s4) and d4 = sqrt2 sin((pi-t)/4) exact.")

# check 1: floors on the ball
r0 = 1/mp.sqrt(5)
worst_p = mp.inf
worst_w = mp.inf
N = 60
for i in range(1, N + 1):
    sp_ = r0*i/N
    Pp = mp.sin(sp_/2)**2
    worst_p = min(worst_p, Pp/sp_**2)
    for j in range(0, N + 1):
        ap = r0*j/N
        Qp = mp.sin(ap/2)**2
        w = Pp + Qp - Pp*Qp/s4**2
        if Pp + Qp > 0:
            worst_w = min(worst_w, w/(Pp + Qp))
print("check 1: min P'/s'^2 = %.4f (>= 0.2458: %s); "
      "min w~/(P'+Q') = %.4f (>= %.4f: %s)"
      % (worst_p, worst_p >= mp.mpf("0.2458"),
         worst_w, 1 - mp.mpf("0.0492")/s4**2,
         worst_w >= 1 - mp.mpf("0.0492")/s4**2 - mp.mpf(10)**-6))
assert worst_p >= mp.mpf("0.2458")
assert worst_w >= 1 - mp.mpf("0.0492")/s4**2 - mp.mpf(10)**-6

# check 2: U-bound vs true mirror-ball mass (kernel at parameter s4)
def K_s4(s, a):
    P = mp.sin(s/2)**2
    Q = mp.sin(a/2)**2
    R2 = 4*(s4**2*(1 - P - Q) + P*Q)
    if R2 <= 0:
        return mp.mpf(0)
    z = 2*beta*mp.sqrt(R2)
    return 2*beta*mp.besseli(1, z)/z

true_mass = mp.quad(lambda s: mp.quad(lambda a: K_s4(s, a),
                                      [0, r0]), [0, r0])*4
Lam = mp.mpf("1.21")/s4**mp.mpf("2.5")
Ubound = Lam*beta**mp.mpf("-1.5")*mp.e**(4*beta*s4)
print("check 2: true mirror-ball mass = %.6e ; U-bound = %.6e ; "
      "dominates: %s (fat factor %.1f)"
      % (true_mass, Ubound, Ubound > true_mass, Ubound/true_mass))
assert Ubound > true_mass, "U-bound FAILS to dominate true mass"

# check 3: assembled M_I at the stress cell vs measured mirror
mstar = mp.mpf("0.5")
Th_m = 12*mp.sqrt(2)/(c*s4)
x = beta*d4
MI = (Lam/mstar)*(4*(c + s4)*(1/s4 + 1/c)*x + Th_m)*mp.e**(-4*x) \
    + (10*mp.sqrt(2)/s4)*(Lam/mstar)**2*beta*mp.e**(-8*x)
measured = mp.mpf("0.0707")
print("check 3: M_I(2.9,15) = %.4f ; measured mirror = %.4f ; "
      "dominates: %s ; slack factor = %.1f (x10 class: < 100)"
      % (MI, measured, MI > measured, MI/measured))
assert MI > measured, "M_I FAILS to dominate the measured mirror"
assert MI/measured < 100, "M_I slack outside the x10 class"

# check 4b: sup x e^{-4x} = 1/(4e)
sup = mp.mpf(1)/(4*mp.e)
print("check 4b: sup x e^(-4x) = 1/(4e) = %.6f ; "
      "beta*d4*e^(-4 beta d4) here = %.6f (<= sup: %s)"
      % (sup, x*mp.e**(-4*x), x*mp.e**(-4*x) <= sup))
print("MIRROR BENCH: ALL CHECKS PASS")
