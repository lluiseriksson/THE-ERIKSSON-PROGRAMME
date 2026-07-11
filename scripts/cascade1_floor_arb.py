"""CASCADE 1 - CERTIFIED floor sweep: m_low(beta_min(t), t) >= 1/2
by interval arithmetic (flint/arb), upgrading the design script's
grid+continuity check to a certificate for the FLOOR CLAIM

    m_low(beta, t) >= 1/2   for beta >= max(15, C_win/(pi-t)),
                                t in (0, pi), C_win = 3/2,

where m_low is the derived closed form of
scripts/cascade1_signed_minoration.py (the CHAIN that m(beta,c) >=
m_low is that script's mathematics, audited separately; this
certificate covers exactly the elementary-function floor).

Structure of the cover (beta-monotonicity of every piece, checked
in the design script and cited in ink, reduces to beta_min(t)):
  SEG-A: t in [1e-9, pi-0.1], beta = 15, 800 intervals (uniform);
         plus the stub t in (0, 1e-9] where c-interval covers it.
  SEG-B: x = pi-t in [1e-3, 0.1], beta = [1.5/x_hi, max(15,1.5/x_lo)]
         hull (a box enclosure of the moving-boundary path), 60
         log-spaced intervals.
  SEG-C: deep tail x in (0, 1e-3]: every beta-dependent factor is
         monotone in x (noted inline); evaluated once with the
         explicitly-bounded exponential tails.

Zone rule for the mirror piece T3 (validity, not sharpness):
  s4_lo >= 0.58          -> Lambda' chain (zone L)
  0.40 <= s4_lo, s4_hi < 0.58 or straddle of 0.58 -> crude C
  otherwise              -> far crude F (valid for all s4)
(zone C valid whenever s4 >= 0.40; zone F valid always on B'.)

Every printed enclosure carries ball + boolean (regime pt 7).
Interval library: python-flint (arb), prec = 120 bits.
"""
import hashlib
import sys
import time

from flint import arb, ctx

ctx.prec = 120

def IV(lo, hi):
    lo = arb(lo); hi = arb(hi)
    return (lo+hi)/2 + ((hi-lo)/2)*arb("0 +/- 1")

def blo(z):
    return arb(z.mid()) - arb(z.rad())

def bhi(z):
    return arb(z.mid()) + arb(z.rad())

# inked constants (decimal strings, exactly the design script's)
CABS_B = arb('1.089'); CABS_M = arb('1.230')
CP = arb('0.2214'); FLB = arb('0.6811'); W0 = arb('0.318')
RB = arb(6)/5; WMAX = 2*(RB/2).sin()**2
SQ2PI = (2*arb.pi()).sqrt()
# GB coefficient COMPUTED from the inked chain constants (audit
# round 1 correction: the hand-assembled 2.0756 understated the
# derived 2*1.0391629... - ghost #23 class; never hand-assemble):
GBC = 2*(1/(4*SQ2PI))*CABS_B*(arb.pi()/4)/(CP*arb('1.9')*FLB)**2
PR2 = (RB/2).sin()**4        # sin^4(0.6) for zone F

def T5_layers(beta, c, bc, zs, pref):
    """Abel-corrected layered rest bound (audit round 2, step 1(d)):
      int_REST phi(w) dA <= phi(v0) Abar_r(v1)
           + sum_{k>=1} phi(v_k) [Abar_r(v_{k+1}) - Abar_r(v_k)],
    the OMITTED bottom-mass term now first (the first layer's mass
    may be all of Abar_r(v1), not just an increment; discrete Abel
    with the REST-restricted CDF vanishing at v0).  phi(v) =
    (1-v)^{-3/4} e^{-2 beta c v}, decreasing on [0.318, 0.9] for
    beta c >= 3.75 (h' = 0.75/(1-v) - 2 beta c < 0 iff 1-v >
    0.375/(beta c)); grid FIXED (beta-independent), truncation
    FIXED at V = 0.9 (cures the moving-truncation monotonicity
    note: every term beta*phi(v_k) is decreasing in beta for
    beta >= 1/(2 c v0) = 2.23, and the {w > 0.9} shard uses
    z <= z_s sqrt(0.1), K = 2 beta A e^z <= beta e^z:
    (2pi)^2 beta^{5/2} e^{-(1-sqrt(0.1)) z_s}, valid for ALL z and
    beta-decreasing).  KERNEL WITNESS on all layers (audit round 3):
    the layer majorant 2 beta e^z/(sqrt(2pi) z^{3/2}) holds for ALL
    z > 0 by the global mini-lemma I_1(z) <= e^z/sqrt(2 pi z)
    (proved in cascade1_signed_minoration.py check (1f'): the
    algebraic factor (1-2u^2)/sqrt(1-u^2) <= 1 iff u^2 <= 3/4, the
    [1/sqrt2, 1] piece is negative, Gaussian completion exact) -
    the companions alone cover only z >= 20, and the window corner
    has layers down to z ~ 13.4.  Abar_r(v) = Abar(v) - 4.006: the disk
    s^2+alpha^2 <= 4 sin^2(0.6) sits inside B with P+Q <=
    (s^2+alpha^2)/4 <= sin^2(0.6) <= v, so its exact area
    4 pi sin^2(0.6) = 4.0064... is B-mass, never REST-mass
    (4.006 rounded down = safe)."""
    def Abar_r(v):
        a = 16*arb.pi()*arb(v)/(1-2*arb(v)).sqrt() if v < 0.418 \
            else 4*arb.pi()**3*arb(v)
        return a - arb('4.006')
    def phi(v):
        return (1-arb(v))**arb('-0.75')*(-2*bc*arb(v)).exp()
    v0 = 0.318; dv = 0.02; V = 0.9
    v = min(v0 + dv, V)
    S = phi(v0)*Abar_r(v)
    while v < V - 1e-12:
        v2 = min(v+dv, V)
        S += phi(v)*(Abar_r(v2)-Abar_r(v))
        v = v2
    shard = (2*arb.pi())**2*beta**arb('2.5') \
        * (-(1-arb('0.1').sqrt())*zs).exp()
    return pref*S + shard

def m_low_arb(t, beta):
    """arb enclosure of m_low on the (t, beta) box."""
    c = (t/4).cos(); s4 = (t/4).sin()
    zs = 4*beta*c; bc = beta*c; d4 = c - s4
    # T1
    br1 = 1 - 3/(8*zs) - arb('0.6')/zs**2
    br2 = 1 - (-bc*RB**2/2).exp() - 3/(8*bc)
    T1 = 2*(SQ2PI/4)/c**arb('2.5')*br1*br2**2
    # T2
    lam = CP*arb('1.9')*FLB*bc
    T2 = -2*(beta/(4*SQ2PI)/c**arb('1.5'))*CABS_B*(arb.pi()/4)/lam**2
    # T3 by zone (validity by s4 bounds)
    s4lo = blo(s4); s4hi = bhi(s4)
    if s4lo >= arb('0.58'):
        q4 = WMAX/(4*s4*s4)
        lamp = CP*arb('1.9')*(1-q4)*beta*s4
        MIR = (beta/(4*SQ2PI)/s4**arb('1.5'))*CABS_M \
              * arb.pi()/lamp*(-4*beta*d4).exp()
    elif s4lo >= arb('0.40'):
        MIR = 4*RB**2*beta**arb('2.5')*(-4*beta*d4).exp()
    else:
        dfar = c - (c*c*PR2 + s4*s4).sqrt()
        MIR = 4*RB**2*beta**arb('2.5')*(-4*beta*dfar).exp()
    T3 = -2*MIR
    # T5
    pref = beta/(4*SQ2PI)/c**arb('1.5')
    T5 = -2*T5_layers(beta, c, bc, zs, pref)
    return T1 + T2 + T3 + T5

print("=== CASCADE 1 floor: CERTIFIED interval sweep ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
import flint
print("python-flint %s  python %s  prec %d bits"
      % (getattr(flint, '__version__', '?'), sys.version.split()[0],
         ctx.prec), flush=True)

t0 = time.time()
HALF = arb(1)/2
allok = True
worst = arb(10)

# SEG-A: t in [1e-9, pi-0.1], beta = 15.  Audit round 3 (A.4): the
# bhi-based rounding was ILLUSORY (the 1e-36 ball radius is dwarfed
# by the 2.2e-16 float half-ulp; float(bhi) == float(blo)); the
# junction is now closed by an EXPLICIT 1e-9 overlap bump on the
# last box (1e-9 >> ulp; SEG-B starts at t = pi - 0.1 <= tb + 1e-9).
NA = 800
ta = 1e-9; tb = float(bhi(arb.pi() - arb('0.1')))
for k in range(NA):
    lo = ta + (tb-ta)*k/NA; hi = ta + (tb-ta)*(k+1)/NA
    if k == NA - 1:
        hi = hi + 1e-9
    v = m_low_arb(IV(lo, hi), arb(15))
    if not bool(blo(v) > HALF):
        allok = False
        print("  SEG-A FAIL at t=[%.6f,%.6f]: [%s, %s]"
              % (lo, hi, blo(v).str(5), bhi(v).str(5)), flush=True)
    if blo(worst) > blo(v):
        worst = v
# stub (0, 1e-9]: t-interval [0, 1e-9] (c-interval covers t -> 0+)
v = m_low_arb(IV(0, 1e-9), arb(15))
ok = bool(blo(v) > HALF)
allok = allok and ok
print("SEG-A (%d intervals + stub): worst enclosure lower %s ; "
      "stub [%s, %s] %s" % (NA, blo(worst).str(6), blo(v).str(5),
      bhi(v).str(5), "True" if allok else "False"), flush=True)

# SEG-B: x = pi - t in [1e-3, 0.1] log-spaced, beta box
NB = 60
worstB = arb(10)
import math
for k in range(NB):
    xlo = 1e-3*(100.0**(k/NB)); xhi = 1e-3*(100.0**((k+1)/NB))
    t_iv = arb.pi() - IV(xlo, xhi)
    blo_beta = 1.5/xhi
    bhi_beta = max(15.0, 1.5/xlo)
    beta_iv = IV(max(15.0, blo_beta), bhi_beta)
    v = m_low_arb(t_iv, beta_iv)
    if not bool(blo(v) > HALF):
        allok = False
        print("  SEG-B FAIL at x=[%.5f,%.5f]: [%s, %s]"
              % (xlo, xhi, blo(v).str(5), bhi(v).str(5)), flush=True)
    if blo(worstB) > blo(v):
        worstB = v
print("SEG-B (%d log intervals): worst enclosure lower %s"
      % (NB, blo(worstB).str(6)), flush=True)

# SEG-C: deep tail x in (0, 1e-3], beta = 1.5/x on the path.
# Monotonicities used (each noted; direction elementary):
#  * 3/(8 z_s) = x/(16 c): increasing in x -> evaluate x-interval;
#  * 0.6/z_s^2 = 0.6 x^2/(36 c^2): same;
#  * e^{-beta c r^2/2} = e^{-1.08 c/x} <= e^{-1.08*0.70/0.001}
#      = e^{-756} < 1e-300 (increasing in x; bound at x = 1e-3);
#  * 3/(8 beta c) = x/(4 c): increasing in x;
#  * |T2| = GBC x /(1.5 c^{7/2}): increasing in x;
#  * 4 beta delta4 = (6/x) sqrt2 sin(x/4) = 1.5 sqrt2 * sinc(x/4)
#      with sinc(y) = sin(y)/y >= 1 - y^2/6: enclosure via
#      1.5 sqrt2 (1 - [0,x^2]/96) - no division by x;
#  * per-layer |T5| terms (1.5/x) e^{-a/x}, a >= 2*0.70*0.318 = 0.44:
#      increasing in x on x <= a; at x = 1e-3: 1500 e^{-445} < 1e-190;
#      30 layers + bridge + shard < 1e-180 total, bounded flat.
x = IV(0, 1e-3)
t_iv = arb.pi() - x
c = (t_iv/4).cos(); s4 = (t_iv/4).sin()
br1 = 1 - x/(16*c) - arb('0.6')*x*x/(36*c*c)
br2 = 1 - IV(0, 1e-300) - x/(4*c)
T1 = 2*(SQ2PI/4)/c**arb('2.5')*br1*br2**2
T2 = -GBC*x/(arb('1.5')*c**arb('3.5'))
q4 = WMAX/(4*s4*s4)
supp = (-(arb('1.5')*arb(2).sqrt())*(1 - x*x/96)).exp()
# Lambda' zone factor at beta s4 >= 1000 (>= the 8.7 the constant
# needs); the lamp rate keeps its beta: MIR/e-supp = A(s4)/(beta s4)
# * beta = A(s4)/s4 ... assembled directly:
lamp_coeff = CP*arb('1.9')*(1-q4)*s4   # times beta
MIR = (1/(4*SQ2PI)/s4**arb('1.5'))*CABS_M*arb.pi()/lamp_coeff*supp
T3 = -2*MIR
T5 = -IV(0, 1e-180)
vC = T1 + T2 + T3 + T5
okC = bool(blo(vC) > HALF)
allok = allok and okC
print("SEG-C deep tail x in (0,1e-3]: enclosure [%s, %s] > 1/2 : %s"
      % (blo(vC).str(6), bhi(vC).str(6), okC), flush=True)

print("\ncertified sweep complete (%.0fs)" % (time.time()-t0))
print("VERDICT: floor m_low >= 1/2 on the whole window : %s"
      % ("CERTIFIED (this transcript, when committed, is the "
         "witness)" if allok else "FAIL - measured failure, "
         "commit with diagnosis"), flush=True)
