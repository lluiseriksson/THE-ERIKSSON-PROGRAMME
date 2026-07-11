"""CASCADE 2b - ZONE-L ADDENDUM to the Step-0 window (v63 item
(iii), fabrication desk): on the Lambda' zone s4 >= 0.58 the mirror
part of <P>/<D> keeps its FULL suppression:

    Theta_mir := (int_{B'} K P)/<D> <= (int_{B'} K)/<D>
              <= C_L e^{-4 beta delta4},   C_L = 4.5 (beta-free),

for beta >= 15, t in [t_L, pi - C_win/beta], where t_L =
4 asin(0.5801) (run 1 placed the edge at s4 = 0.58 exactly and the
edge guard failed by enclosure slop at the float boundary - fail1
transcript preserved; the inked zone is s4 >= 0.5801, comfortably
containing every client: the stress cell has s4 = 0.6627, and the
zone-L formula's validity s4 >= 0.58 strictly contains the claim).  Combined with the inked rem:step0
this sharpens the mirror term of |E - C| and of the mu_F chain by
e^{+2 beta delta4} where it matters (stress cell: e^{-2 b d4} =
0.077 vs e^{-4 b d4} = 0.006 - a factor 12.9; the additive client
constant becomes 12 C_L e^{-4 beta delta4}).

CHAIN (all committed pieces): int_{B'} K <= MIRC e^{-4 beta delta4}
with MIRC the zone-L coefficient of cascade 1 (beta-FREE:
the beta in the prefactor cancels against the rate);
<D> >= m_low (lem:mass, certified).  So the claim reduces to
    MIRC(s4)/m_low(beta, t) <= C_L   on the zone,
whose worst case is beta = beta_min(t) (MIRC beta-free, m_low
beta-increasing - cascade 1's certified monotonicity).  Certified
below by the same arb segment machinery (SEG-A zone part, SEG-B,
SEG-C deep tail where the ratio is beta-free).

Transcript exists when committed.  No sympy.
"""
import hashlib
import math
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

CABS_B = arb('1.089'); CABS_M = arb('1.230')
CP = arb('0.2214'); FLB = arb('0.6811')
RB = arb(6)/5; WMAX = 2*(RB/2).sin()**2
SQ2PI = (2*arb.pi()).sqrt()
PR2 = (RB/2).sin()**4
C_L = arb('4.5')

def m_low_and_mirc(t, beta):
    c = (t/4).cos(); s4 = (t/4).sin()
    zs = 4*beta*c; bc = beta*c; d4 = c - s4
    br1 = 1 - 3/(8*zs) - arb('0.6')/zs**2
    br2 = 1 - (-bc*RB**2/2).exp() - 3/(8*bc)
    T1 = 2*(SQ2PI/4)/c**arb('2.5')*br1*br2**2
    lam = CP*arb('1.9')*FLB*bc
    GB = (beta/(4*SQ2PI)/c**arb('1.5'))*CABS_B*(arb.pi()/4)/lam**2
    q4 = WMAX/(4*s4*s4)
    lamp = CP*arb('1.9')*(1-q4)*beta*s4
    MIRC = (beta/(4*SQ2PI)/s4**arb('1.5'))*CABS_M*arb.pi()/lamp
    MIR = MIRC*(-4*beta*d4).exp()
    def Abar_r(v):
        a = 16*arb.pi()*arb(v)/(1-2*arb(v)).sqrt() if v < 0.418 \
            else 4*arb.pi()**3*arb(v)
        return a - arb('4.006')
    def phi(v):
        return (1-arb(v))**arb('-0.75')*(-2*bc*arb(v)).exp()
    v0 = 0.318; dv = 0.02; V = 0.9
    v = v0 + dv
    S = phi(v0)*Abar_r(v)
    while v < V - 1e-12:
        v2 = min(v+dv, V)
        S += phi(v)*(Abar_r(v2)-Abar_r(v))
        v = v2
    pref = beta/(4*SQ2PI)/c**arb('1.5')
    REST = pref*S + (2*arb.pi())**2*beta**arb('2.5') \
        * (-(1-arb('0.1').sqrt())*zs).exp()
    m_low = T1 - 2*GB - 2*MIR - 2*REST
    return m_low, MIRC

print("=== CASCADE 2b: zone-L full-suppression addendum ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
import flint
print("python-flint %s  python %s  prec %d  claim: MIRC/m_low <= %s "
      "on s4 >= 0.5801" % (getattr(flint, '__version__', '?'),
                           sys.version.split()[0], ctx.prec, C_L),
      flush=True)

t0 = time.time()
allok = True
worst = arb(-10)
tL = float(4*math.asin(0.5801))     # inked zone edge ~ 2.4754

def test(t_iv, beta_iv, tag):
    global allok, worst
    m_low, MIRC = m_low_and_mirc(t_iv, beta_iv)
    if not bool(blo(m_low) > 0):
        allok = False
        print("  %s m_low not positive" % tag, flush=True)
        return
    ratio = MIRC/m_low
    if not bool(bhi(ratio) < C_L):
        allok = False
        print("  %s FAIL: [%s, %s]" % (tag, blo(ratio).str(5),
              bhi(ratio).str(5)), flush=True)
    if bhi(worst) < bhi(ratio):
        worst = ratio

# SEG-A zone part: t in [tL, pi - 0.1], beta = 15 (monotonicity:
# MIRC beta-free, m_low beta-increasing => ratio beta-decreasing)
NA = 200
tb = float(bhi(arb.pi() - arb('0.1')))
for k in range(NA):
    lo = tL + (tb-tL)*k/NA; hi = tL + (tb-tL)*(k+1)/NA
    if k == NA - 1:
        hi = hi + 1e-9      # junction overlap into SEG-B
    test(IV(lo, hi), arb(15), "SEG-A[%d]" % k)
# guard the zone edge itself: one box straddling tL from below is
# NOT claimed (the claim starts at s4 >= 0.58; boxes start at tL,
# whose s4 enclosure's lower end must be >= 0.58 - checked):
s4_edge = (IV(tL, tL)/4).sin()
print("SEG-A done: zone-edge s4 enclosure lower %s (need >= 0.58: "
      "%s); worst ratio [%s, %s]"
      % (blo(s4_edge).str(8), bool(blo(s4_edge) > arb('0.58')),
         blo(worst).str(5), bhi(worst).str(5)), flush=True)
allok = allok and bool(blo(s4_edge) > arb('0.58'))

# SEG-B: moving boundary
NB = 200
for k in range(NB):
    xlo = 1e-3*(100.0**(k/NB)); xhi = 1e-3*(100.0**((k+1)/NB))
    t_iv = arb.pi() - IV(xlo, xhi)
    beta_iv = IV(max(15.0, math.nextafter(1.5/xhi, 0.0)),
                 max(15.0, 1.5/xlo))
    test(t_iv, beta_iv, "SEG-B[%d]" % k)
print("SEG-B done: worst ratio [%s, %s]"
      % (blo(worst).str(5), bhi(worst).str(5)), flush=True)

# SEG-C deep tail x in (0, 1e-3]: MIRC/m_low is beta-free there
# (cascade-1 SEG-C reductions; m_lowC as in the committed scripts)
x = IV(0, 1e-3)
t_iv = arb.pi() - x
c = (t_iv/4).cos(); s4 = (t_iv/4).sin()
br1 = 1 - x/(16*c) - arb('0.6')*x*x/(36*c*c)
br2 = 1 - IV(0, 1e-300) - x/(4*c)
T1 = 2*(SQ2PI/4)/c**arb('2.5')*br1*br2**2
GBC2 = 2*(1/(4*SQ2PI))*CABS_B*(arb.pi()/4)/(CP*arb('1.9')*FLB)**2
T2 = -GBC2*x/(arb('1.5')*c**arb('3.5'))
q4 = WMAX/(4*s4*s4)
supp4 = (-(arb('1.5')*arb(2).sqrt())*(1 - x*x/96)).exp()
lampc = CP*arb('1.9')*(1-q4)*s4
MIRu = (1/(4*SQ2PI)/s4**arb('1.5'))*CABS_M*arb.pi()/lampc
m_lowC = T1 + T2 - 2*MIRu*supp4 - IV(0, 1e-180)
ratioC = MIRu/m_lowC
okC = bool(bhi(ratioC) < C_L) and bool(blo(m_lowC) > 0)
allok = allok and okC
print("SEG-C: ratio [%s, %s] : %s"
      % (blo(ratioC).str(5), bhi(ratioC).str(5), okC), flush=True)

print("\nsweep complete (%.0fs)" % (time.time()-t0))
print("VERDICT: %s" % (("CERTIFIED: Theta_mir <= %s e^{-4 beta "
      "delta4} on the zone s4 >= 0.5801" % C_L) if allok
      else "FAIL - measured failure, commit with diagnosis"),
      flush=True)
