"""CASCADE 2 - THE STEP-0 WINDOW EPSILON (fabrication desk).

Target (rem:step0, acta v58 pt 2): the pending moment bound, now in
its HONEST form (the mirror is additive, exactly as the truth is):

    <P>_K / <D>  <=  [4 beta c]^{-1} (1 + eps_b)  +  C_mir e^{-2 beta delta4}

for beta >= 15, t in (0, pi - C_win/beta], with CERTIFIED constants
(eps_b, C_mir).  Client (lem:mini(b), |F| <= 12P):

    |E - C| <= (3/(beta c))(1 + eps_b) + 12 C_mir e^{-2 beta delta4},

and the mu_F chain of lem:extraction(v) inherits the same two terms
in place of the crude 34.2/(beta c).

WHY NOT the naive [4 beta c]^{-1}(1+eps) with one eps: near t -> pi
the mirror mass sits at P ~ 1 and contributes ~ e^{-4 beta delta4}
= O(1) on the moving boundary, while [4 beta c]^{-1} -> 0 there: a
multiplicative eps would have to DIVERGE like beta e^{-2.12}.  The
additive form is what is true.  (Recorded in acta v61's cascade-2
note BEFORE this fabrication.)

ROUTE: pure corollary of Cascade 1's committed chains (identical
constants, same safe-side roundings; scripts/cascade1_*):
    <P> <= GB/2 + MIR + REST,  <D> >= m_low  (certified >= 1/2),
where int_B K P = (1/2) int_B K(P+Q) by the s<->alpha symmetry of
K and B, and P <= 1 pays the off-B masses.  Then
    eps_b  witnesses  4 beta c (GB/2 + REST)/m_low - 1,
    C_mir  witnesses  MIR e^{2 beta delta4}/m_low, per mirror zone:
      zone L (s4>=0.58): MIRC e^{-2 beta delta4}/m_low, MIRC beta-
        free, e^{-2 beta delta4} at beta_min (monotone);
      zone C (0.40<=s4<0.58): 4 r^2 beta^{5/2} e^{-2 beta delta4}
        /m_low, decreasing in beta (delta4 >= 0.2346 > 5/(4*15));
      zone F (s4<0.40): 4 r^2 beta^{5/2} e^{-2 beta (2 dfar -
        delta4)}/m_low with 2 dfar - delta4 > 0 on the zone
        (checked), decreasing in beta.
Certified by the same arb segment sweep as cascade1_floor_arb.py
(SEG-A/B and the deep tail SEG-C, where every ratio is beta-free or
hand-monotone; the additive form has NO divergence anywhere).

Inked candidates under test (safe-side), TWO-ZONE in t (the bulk
client - num_2's eight-cell table, the stress cell, the mu_F cut -
lives at t <= 2.9; the boundary strip pays its own honest constant):
    eps_b = 2.0 for t <= 2.9;  eps_b = 4.85 for t > 2.9;
    C_mir = 3.0 everywhere.
FAILURE HISTORY (measured, preserved):
  run 1 (fail1 transcript): eps_b = 4.2 uniform - SEG-B boxes 57-59
    reached 6.78 (box-pairing slop at hull ratio 100^{1/60} + the
    real boundary peak where GB ~ c^{-7/2} meets m_low's dip);
    repair: 200 SEG-B boxes + zoned constants.
  run 2 (fail2 transcript): eps_b(bulk) = 1.75 too tight - the true
    curve reaches 1.955 just below t = 2.9; and SEG-B[199] box gave
    4.748 > 4.7.  Repair: ceilings 2.0/4.85.
  audit round 1 (cascade1_audit_transcript.txt): the hand-assembled
    GB constant 1.0378 does not re-derive (chain: 1.0391629); this
    script now COMPUTES the coefficient (GBC2) from the inked chain
    constants - nothing hand-assembled remains.
Bench: true <P>/<D> by quadrature at seven cells (verified,
calibration only).

Regime: no sympy; transcript exists when committed.
"""
import hashlib
import sys
import time

import mpmath as mp
from flint import arb, ctx

ctx.prec = 120

def IV(lo, hi):
    lo = arb(lo); hi = arb(hi)
    return (lo+hi)/2 + ((hi-lo)/2)*arb("0 +/- 1")

def blo(z):
    return arb(z.mid()) - arb(z.rad())

def bhi(z):
    return arb(z.mid()) + arb(z.rad())

# Cascade-1 inked constants (byte-identical values)
CABS_B = arb('1.089'); CABS_M = arb('1.230')
CP = arb('0.2214'); FLB = arb('0.6811')
RB = arb(6)/5; WMAX = 2*(RB/2).sin()**2
SQ2PI = (2*arb.pi()).sqrt()
PR2 = (RB/2).sin()**4

EPS_B_BULK = arb('2.0')    # t <= 2.9 (run 2 measured 1.955 at the
                           # zone edge; 1.75 was too tight)
EPS_B_EDGE = arb('4.85')   # t > 2.9 (run 2: SEG-B[199] box 4.748)
C_MIR = arb('3.0')
# GB coefficient COMPUTED from the chain constants (audit round 1:
# never hand-assemble; 2*1.0391629... not 2.0756):
GBC2 = 2*(1/(4*(2*arb.pi()).sqrt()))*arb('1.089')*(arb.pi()/4) \
       / (arb('0.2214')*arb('1.9')*arb('0.6811'))**2

def rest_layers(beta, c, bc, zs):
    wz_lo = float(blo(1 - (20/zs)**2)); wz_hi = float(bhi(1 - (20/zs)**2))
    S = arb(0); v = 0.318; dv = 0.02
    while v < wz_lo:
        v2 = min(v+dv, wz_lo)
        Ab2 = 16*arb.pi()*arb(v2)/(1-2*arb(v2)).sqrt() \
            if v2 < 0.418 else 4*arb.pi()**3*arb(v2)
        Ab1 = 16*arb.pi()*arb(v)/(1-2*arb(v)).sqrt() \
            if v < 0.418 else 4*arb.pi()**3*arb(v)
        S += (1-arb(v2))**arb('-0.75')*(-2*bc*arb(v)).exp()*(Ab2-Ab1)
        v = v2
    S += (bhi(zs)/20)**arb('1.5')*(-2*bc*arb(wz_lo)).exp() \
         * (4*arb.pi()**3)*arb(wz_hi-wz_lo if wz_hi > wz_lo else 0)
    pref = beta/(4*SQ2PI)/c**arb('1.5')
    return pref*S + (2*arb.pi())**2*beta**arb('2.5')*(arb(20)-zs).exp()

def assemble(t, beta):
    """(BALL=GB/2+REST, MIR2 = MIR e^{2 beta d4}, m_low) enclosures."""
    c = (t/4).cos(); s4 = (t/4).sin()
    zs = 4*beta*c; bc = beta*c; d4 = c - s4
    br1 = 1 - 3/(8*zs) - arb('0.6')/zs**2
    br2 = 1 - (-bc*RB**2/2).exp() - 3/(8*bc)
    T1 = 2*(SQ2PI/4)/c**arb('2.5')*br1*br2**2
    lam = CP*arb('1.9')*FLB*bc
    GB = (beta/(4*SQ2PI)/c**arb('1.5'))*CABS_B*(arb.pi()/4)/lam**2
    REST = rest_layers(beta, c, bc, zs)
    s4lo = blo(s4)
    if s4lo >= arb('0.58'):
        q4 = WMAX/(4*s4*s4)
        lamp = CP*arb('1.9')*(1-q4)*beta*s4
        MIRC = (beta/(4*SQ2PI)/s4**arb('1.5'))*CABS_M*arb.pi()/lamp
        MIR = MIRC*(-4*beta*d4).exp()
        MIR2 = MIRC*(-2*beta*d4).exp()
    elif s4lo >= arb('0.40'):
        MIR = 4*RB**2*beta**arb('2.5')*(-4*beta*d4).exp()
        MIR2 = 4*RB**2*beta**arb('2.5')*(-2*beta*d4).exp()
    else:
        dfar = c - (c*c*PR2 + s4*s4).sqrt()
        MIR = 4*RB**2*beta**arb('2.5')*(-4*beta*dfar).exp()
        MIR2 = 4*RB**2*beta**arb('2.5')*(-2*beta*(2*dfar-d4)).exp()
        if not bool(blo(2*dfar - d4) > 0):
            return None  # zone-F positivity violated: report
    m_low = T1 - 2*GB - 2*MIR - 2*REST
    return GB/2 + REST, MIR2, m_low, bc

print("=== CASCADE 2: Step-0 window epsilon (additive mirror form) ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
import flint
print("python-flint %s  mpmath %s  python %s  prec %d"
      % (getattr(flint, '__version__', '?'), mp.__version__,
         sys.version.split()[0], ctx.prec), flush=True)
print("inked claim: <P>/<D> <= [4 beta c]^{-1}(1+eps_b) + "
      "C_mir e^{-2 beta delta4}; eps_b = %s (t<=2.9) / %s (t>2.9), "
      "C_mir = %s" % (EPS_B_BULK, EPS_B_EDGE, C_MIR), flush=True)

t0 = time.time()
allok = True
worst_eb = arb(-10); worst_cm = arb(-10)

def test_box(t_iv, beta_iv, tag):
    global allok, worst_eb, worst_cm
    out = assemble(t_iv, beta_iv)
    if out is None:
        allok = False
        print("  %s zone-F positivity FAIL" % tag, flush=True)
        return
    BALL, MIR2, m_low, bc = out
    if not bool(blo(m_low) > 0):
        allok = False
        print("  %s m_low not positive" % tag, flush=True)
        return
    eb = 4*bc*BALL/m_low - 1
    cm = MIR2/m_low
    # zone: BULK iff the box lies wholly at t <= 2.9 (+1e-7 float
    # guard so the breakpoint box itself counts as bulk; the edge
    # zone starts at the next box, whose bhi exceeds the guard)
    ceiling = EPS_B_BULK if bool(bhi(t_iv) <= arb('2.9000001')) \
        else EPS_B_EDGE
    if not bool(bhi(eb) < ceiling):
        allok = False
        print("  %s EPS_B FAIL vs %s: [%s, %s]" % (tag, ceiling,
              blo(eb).str(5), bhi(eb).str(5)), flush=True)
    if not bool(bhi(cm) < C_MIR):
        allok = False
        print("  %s C_MIR FAIL: [%s, %s]" % (tag, blo(cm).str(5),
              bhi(cm).str(5)), flush=True)
    if bhi(worst_eb) < bhi(eb):
        worst_eb = eb
    if bhi(worst_cm) < bhi(cm):
        worst_cm = cm

# beta-monotonicity of the two ratios (cited, then numerically
# confirmed below): numerator pieces GB/2, REST, MIR2 are each
# beta-decreasing (Cascade-1 witnesses; MIR2's e^{-2 beta d4}
# variants shown in the docstring) while 4 beta c * GB/2 is beta-
# FREE (= 2*1.0378/c^{5/2}) and 4 beta c * REST decays; m_low is
# beta-increasing (Cascade 1).  So beta = beta_min(t) is worst.
# SEG-A grid puts a breakpoint AT t = 2.9 so the bulk zone's
# certificate covers exactly t <= 2.9 (no straddling box).
NA1 = 740; NA2 = 60
ta = 1e-9; tm = 2.9; tb = float(blo(arb.pi() - arb('0.1')))
for k in range(NA1):
    lo = ta + (tm-ta)*k/NA1; hi = ta + (tm-ta)*(k+1)/NA1
    test_box(IV(lo, hi), arb(15), "SEG-A[%d]" % k)
for k in range(NA2):
    lo = tm + (tb-tm)*k/NA2; hi = tm + (tb-tm)*(k+1)/NA2
    test_box(IV(lo, hi), arb(15), "SEG-A2[%d]" % k)
test_box(IV(0, 1e-9), arb(15), "SEG-A[stub]")
print("SEG-A: worst eps_b <= %s, worst C_mir witness <= %s"
      % (bhi(worst_eb).str(6), bhi(worst_cm).str(6)), flush=True)

NB = 200
for k in range(NB):
    xlo = 1e-3*(100.0**(k/NB)); xhi = 1e-3*(100.0**((k+1)/NB))
    t_iv = arb.pi() - IV(xlo, xhi)
    beta_iv = IV(max(15.0, 1.5/xhi), max(15.0, 1.5/xlo))
    test_box(t_iv, beta_iv, "SEG-B[%d]" % k)
print("SEG-B: worst eps_b <= %s, worst C_mir witness <= %s"
      % (bhi(worst_eb).str(6), bhi(worst_cm).str(6)), flush=True)

# SEG-C deep tail x = pi - t in (0, 1e-3], zone L (s4 -> sqrt2/2):
# every ratio is beta-free or hand-monotone (Cascade-1 SEG-C notes):
# 4 beta c GB/2 = 2*1.0378/c^{5/2}; 4 beta c REST < 1e-170;
# MIR2/m_low = MIRC e^{-2 beta d4}/m_low with 2 beta d4 >=
# 0.75 sqrt2 (1-x^2/96) (half the Cascade-1 sinc bound), MIRC/m_low
# beta-free.
x = IV(0, 1e-3)
t_iv = arb.pi() - x
c = (t_iv/4).cos(); s4 = (t_iv/4).sin()
br1 = 1 - x/(16*c) - arb('0.6')*x*x/(36*c*c)
br2 = 1 - IV(0, 1e-300) - x/(4*c)
T1 = 2*(SQ2PI/4)/c**arb('2.5')*br1*br2**2
T2 = -GBC2*x/(arb('1.5')*c**arb('3.5'))
q4 = WMAX/(4*s4*s4)
supp4 = (-(arb('1.5')*arb(2).sqrt())*(1 - x*x/96)).exp()
supp2 = (-(arb('0.75')*arb(2).sqrt())*(1 - x*x/96)).exp()
lampc = CP*arb('1.9')*(1-q4)*s4
MIRu = (1/(4*SQ2PI)/s4**arb('1.5'))*CABS_M*arb.pi()/lampc
m_lowC = T1 + T2 - 2*MIRu*supp4 - IV(0, 1e-180)
ebC = GBC2/c**arb('2.5')/m_lowC - 1 + IV(0, 1e-170)
cmC = MIRu*supp2/m_lowC
okC = bool(bhi(ebC) < EPS_B_EDGE) and bool(bhi(cmC) < C_MIR) \
      and bool(blo(m_lowC) > 0)
allok = allok and okC
print("SEG-C deep tail: eps_b [%s, %s], C_mir witness [%s, %s] : %s"
      % (blo(ebC).str(5), bhi(ebC).str(5), blo(cmC).str(5),
         bhi(cmC).str(5), okC), flush=True)

print("\ncertified sweep complete (%.0fs)" % (time.time()-t0))
print("VERDICT (floor of the claim): %s"
      % ("CERTIFIED with eps_b = (%s bulk / %s edge), C_mir = %s"
         % (EPS_B_BULK, EPS_B_EDGE, C_MIR)
         if allok else "FAIL - measured failure, commit with "
         "diagnosis"), flush=True)

# ----------------------------------------------------------------
print("\n--- bench vs truth (verified, calibration only) ---")
mp.mp.dps = 15

def true_ratio(beta, t):
    beta = mp.mpf(beta); t = mp.mpf(t)
    c = mp.cos(t/4); s4 = mp.sin(t/4); zs = 4*beta*c
    def kern(s, a):
        P = mp.sin(s/2)**2; Q = mp.sin(a/2)**2
        R2 = 4*c*c*(1-P)*(1-Q) + 4*s4*s4*P*Q
        z = 2*beta*mp.sqrt(R2)
        return (2*beta**mp.mpf('2.5')*(mp.besseli(1, z)/mp.e**z/z)
                * mp.e**(z-zs)), P, Q
    def wq(w, xs, ys):
        return 4*mp.quad(lambda s: mp.quad(lambda a: w(*kern(s, a)),
                                           ys), xs)
    r = 1.2
    regs = [([0, r/2, r], [0, r/2, r]),
            ([mp.pi-r, mp.pi-r/2, mp.pi], [mp.pi-r, mp.pi-r/2, mp.pi]),
            ([r, 2, mp.pi], [0, r]), ([0, r], [r, 2, mp.pi]),
            ([r, 2, mp.pi-r], [r, 2, mp.pi-r]),
            ([mp.pi-r, mp.pi], [r, 2, mp.pi-r]),
            ([r, 2, mp.pi-r], [mp.pi-r, mp.pi])]
    p = sum(wq(lambda k, P, Q: k*P, *xy) for xy in regs)
    d = sum(wq(lambda k, P, Q: k*2*(1-P-Q), *xy) for xy in regs)
    return p/d

for (tt, bb) in [(0.5, 15), (1.5, 15), (2.5, 15), (2.9, 15),
                 (3.0416, 15), (1.5, 30), (3.1, 36.05)]:
    tr = true_ratio(bb, tt)
    c = mp.cos(mp.mpf(tt)/4); s4 = mp.sin(mp.mpf(tt)/4)
    d4 = c - s4
    eb_cell = EPS_B_BULK if tt <= 2.9 else EPS_B_EDGE
    bound = (1+float(bhi(eb_cell)))/(4*bb*c) \
            + float(bhi(C_MIR))*mp.e**(-2*bb*d4)
    print("  (%.4g,%.4g): true <P>/<D> = %s, bound %s, slack x%.2f %s"
          % (tt, bb, mp.nstr(tr, 5), mp.nstr(mp.mpf(bound), 5),
             float(bound/tr), "OK" if bound >= tr else
             "DOMINANCE FAIL"), flush=True)
print("done (%.0fs total)" % (time.time()-t0), flush=True)
