"""CASCADE 1 - THE SIGNED MINORATION (fabrication desk).

Target (acta v35/v58): discharge the candidate lem:mass by proving
    m(beta,c) := beta^{3/2} e^{-4 beta c} <D>  >=  1/2
for beta >= 15, t in (0, pi - C_win/beta], C_win = 3/2, with
c = cos(t/4), s4 = sin(t/4), <D> = iint_{[-pi,pi]^2} K D ds dalpha
(conv:mass, unnormalized), K = 2 beta I_1(z)/z, z = 2 beta R,
R^2 = 4c^2(1-w), w = P + Q - PQ/c^2 (exact), z_s = 4 beta c,
D = cos s + cos alpha = 2(1 - P - Q) (exact),
P = sin^2(s/2), Q = sin^2(alpha/2).

ROUTE (v35 dissolution + the mirror/rest treatment this desk owes):
split the torus into
  B    = [-r, r]^2,               r  = 6/5   (main rectangle)
  B'   = {|s|>=pi-r', |a|>=pi-r'}, r' = 6/5  (mirror rectangle)
  REST = the complement.
On B the identity K D = 2K - 2K(P+Q) is EXACT (nothing signed is
bounded by absolutes where the cancellation lives); off B we pay
|D| <= 2:
  <D> >= 2*MU1LOW - 2*GB_UP - 2*MIRROR_UP - 2*REST_UP.

The four chains (every constant DERIVED, no fits; two-term Bessel
companions and mini-lemma (a) are CITED from the inked manuscript):

[T1] MU1LOW (lower bound of int_B K, integrand positive):
  z >= 20 on B  (z >= z_s sqrt(1-wmax) >= 0.60196*z_s >= 25.5);
  I_1(z) >= e^z/sqrt(2 pi z) (1 - 3/(8z) - 0.6/z^2)   [companions];
  z <= z_s globally (mini-lemma (a), c^2 >= 1/2), and
  x^{-3/2}(1 - a/x - b/x^2) is decreasing in x = z/z_s on the range
  (checked below), so the bracket may be frozen at z = z_s;
  exponent: z - z_s = z_s(sqrt(1-w) - 1) >= -z_s(w/2 + w^2/4) for
  w <= 0.7 (root from below, 4u + u^2 <= 4 iff u <= 2(sqrt2 - 1));
  w <= P+Q, w^2 <= (P+Q)^2 <= 2(P^2+Q^2), P <= s^2/4: the Gaussian
  factorizes per variable with quartic penalty e^{-beta c s^4/8};
  e^{-x} >= 1-x on the quartic; erfc(x) <= e^{-x^2} for the window;
  exact Gaussian moments.  Result:
    MU1LOW_m = (sqrt(2 pi)/4) c^{-5/2} (1 - 3/(8 z_s) - 0.6/z_s^2)
               * (1 - e^{-beta c r^2/2} - 3/(8 beta c))^2
  (m-units: every integral carries beta^{3/2} e^{-z_s}).

[T2] GB_UP (upper bound of int_B K(P+Q)):
  I_1(z) <= e^z/sqrt(2 pi z) for z >= 20 [companions, upper];
  prefactor z^{-3/2} = z_s^{-3/2}(1-w)^{-3/4};
  exponent: e^{z - z_s} <= e^{-2 beta c w} (root from above);
  absorption (convexity, endpoint max):
    (1-w)^{-3/4} e^{-0.1*betac_min*w} <= C_abs on [0, wmax]
  so (1-w)^{-3/4} e^{-2 beta c w} <= C_abs e^{-1.9 beta c w};
  w >= (P+Q)(1 - (P+Q)/(4c^2)) >= 0.6812(P+Q) on B (c^2 >= 1/2);
  P >= 0.2214 s^2 on |s| <= r (concavity of sin on [0, 0.6]);
  P+Q <= (s^2 + alpha^2)/4 in front; exact Gamma moments.  Result:
    GB_m <= (beta/(4 sqrt(2 pi)) / c^{3/2}) * C_abs * (pi/4)
            / (0.2214 * 1.9 * 0.6811 * beta c)^2
          = 1.0392/(beta c^{7/2})   (rounded UP from the computed
            1.0391629...; audit round 1 caught a hand-assembled
            1.0378 here - constants are COMPUTED, never assembled).

[T3] MIRROR_UP (upper bound of int_{B'} K), three zones in s4:
  mirror chart (exact): 1 - w = (s4/c)^2 (1 - w'),
  w' = P'+Q'-P'Q'/s4^2, P' = sin^2(s'/2), s' = pi - s; hence
  z = z_s(s4) sqrt(1-w'), z_s(s4) = 4 beta s4, and the relative
  suppression e^{z_s(s4) - z_s(c)} = e^{-4 beta delta4} is exact.
  zone L (s4 >= 0.58): same chain as [T2] in the mirror chart
    (z >= 0.58*60*0.60196 > 20 at beta >= 15; w' in [0, wmax] on B'
    needs s4 >= 0.4: min(P',Q') <= sin^2(0.6)/2 <= s4^2);
    rate floor w' >= (P'+Q')(1 - wmax/(4 s4^2)) =: (1-q4)(P'+Q').
    MIRROR_m <= (beta/(4 sqrt(2 pi)) / s4^{3/2}) * C'_abs
                * pi/(0.2214*1.9*(1-q4) beta s4) * e^{-4 beta delta4}
  zone C (0.4 <= s4 < 0.58): z <= z_s(s4) on B' (w' >= 0 there),
    K = 2 beta A(z) e^z <= beta e^{z_s(s4)} (A <= 1/2):
    MIRROR_m <= Area(B') beta^{5/2} e^{-4 beta delta4},
    delta4 >= c - s4 >= 0.2346 in the zone: dead.
  zone F (s4 < 0.4): on B', R^2 <= 4c^2 sin^4(0.6) + 4 s4^2 wait -
    R^2 = 4c^2(1-P)(1-Q) + 4 s4^2 PQ <= 4c^2 sin^4(r'/2) + 4 s4^2,
    so z - z_s <= -4 beta (c - sqrt(c^2 sin^4(0.6) + s4^2)): dead
    (Delta_far >= 0.42 in the zone).

[T5] REST_UP (upper bound of int_REST K):
  w-floor: w >= P+Q-2PQ =: g (c^2 >= 1/2) and on REST
  g >= min(sin^2(r/2), 1-cos^2(r'/2), 2q(1-q)) = sin^2(0.6) =: w0
  (case analysis below);
  area lemma (exact Beta integral): the measure ds dalpha pushed to
  (P,Q) is dP dQ/sqrt(PQ(1-P)(1-Q)) per quarter, so
    Area({P+Q <= u}) <= 4 pi u / sqrt(1-u),
  same in the mirror chart; both components:
    Abar(v) := min(16 pi v/sqrt(1-2v) [v < 1/2], 4 pi^3 v)
    (global branch via P >= (s/pi)^2; the MIN form after the
    external audit on 0794fb3 - true crossover (1-16/pi^4)/2,
    min of two increasing branches is nondecreasing),
    Area({w<=v}) <= Abar(v); REST-sharpening: the disk
    s^2+alpha^2 <= 4 sin^2(0.6) lies in B with P+Q <= sin^2(0.6),
    so Abar_r(v) := Abar(v) - 4.006 bounds the REST-restricted CDF
    (4 pi sin^2(0.6) = 4.0064, rounded down);
  ABEL-CORRECTED layer sum (audit round 2: the plain increment sum
  omitted the bottom-mass term - the first layer's mass may be all
  of Abar_r(v1)); kernel majorant K <= 2 beta e^z/(sqrt(2pi) z^{3/2})
  on ALL layers by the GLOBAL mini-lemma I_1(z) <= e^z/sqrt(2 pi z),
  z > 0 (check (1f'); audit round 3 - the companions alone witness
  only z >= 20, and the window corner has layers down to z ~ 13.4):
  with phi(v) = (1-v)^{-3/4} e^{-2 beta c v},
  decreasing on [0.318, 0.9] for beta c >= 3.75,
    REST_m <= pref_m * [ phi(v0) Abar_r(v1)
              + sum_{k>=1} phi(v_k)(Abar_r(v_{k+1}) - Abar_r(v_k)) ]
  on the FIXED grid v0 = 0.318 step 0.02 to V = 0.9, plus the
  {w > 0.9} shard (z <= z_s sqrt(0.1), K <= beta e^z):
    REST_shard_m <= (2 pi)^2 beta^{5/2} e^{-(1-sqrt(0.1)) z_s};
  every term beta phi(v_k) and the shard are beta-DECREASING
  (fixed truncation: the moving-truncation note is void).

BETA-MONOTONICITY: every piece of m_low is nondecreasing in beta at
fixed t for beta >= 15 (checked piecewise below), so the infimum
sits on the moving-boundary path beta_min(t) = max(15, C_win/(pi-t))
- a ONE-dimensional sweep.

STATUS LABELS: the assembled m_low is a DERIVED closed form; the
in-script checks of each elementary link are design verification of
exact claims; the truth quadratures of PART 4 are 'verified'
numerics (calibration of slack, bearing no load).  Nothing here is
'certified' (no interval arithmetic is claimed).

Regime notes: no sympy.series anywhere (no sympy at all); constants
rounded in the SAFE direction before use (what is verified is what
will be inked); transcript exists when committed.
"""
import hashlib
import sys
import time

import mpmath as mp

mp.mp.dps = 25

PASS = []
def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    PASS.append(ok)
    print("[%s] %s %s" % (tag, name, detail), flush=True)

# ---------------------------------------------------------------
# frozen design parameters (exact rationals where possible)
R_BALL = mp.mpf(6)/5          # r = r' = 1.2
CWIN   = mp.mpf(3)/2
BETA1  = mp.mpf(15)
PR     = mp.sin(R_BALL/2)**2   # sin^2(0.6) = 0.318821...
WMAX   = 2*PR                  # 0.637642...
W0_INK = mp.mpf('0.318')       # inked rest floor (rounded DOWN)
CP_INK = mp.mpf('0.2214')      # inked concavity floor P >= CP s^2
BETAC_MIN = BETA1/mp.sqrt(2)   # 10.6066...
S4_L   = mp.mpf('0.58')        # Lambda'-zone edge
S4_C   = mp.mpf('0.40')        # crude-zone edge

print("=== CASCADE 1: signed minoration, fabrication transcript ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("mpmath %s  python %s" % (mp.__version__, sys.version.split()[0]))
print("params: r=r'=%s  wmax=%s  w0_ink=%s  cp_ink=%s  s4_L=%s"
      % (R_BALL, mp.nstr(WMAX, 8), W0_INK, CP_INK, S4_L), flush=True)

# ---------------------------------------------------------------
print("\n--- PART 1: elementary links (each an exact claim; design "
      "check on fine grids / by convexity) ---")

# (1a) root from below: sqrt(1-u) >= 1 - u/2 - u^2/4 on [0, 0.7]
ok = True
for k in range(7001):
    u = mp.mpf(k)/10000
    if mp.sqrt(1-u) < 1 - u/2 - u*u/4 - mp.mpf(10)**-35:
        ok = False; break
check("(1a) sqrt(1-u) >= 1-u/2-u^2/4 on [0,0.7]", ok,
      "(4u+u^2<=4 iff u<=2(sqrt2-1)=0.8284)")

# (1b) concavity floor: P = sin^2(s/2) >= CP_INK * s^2 on |s| <= r
ok = True
for k in range(1, 12001):
    s = R_BALL*mp.mpf(k)/12000
    if mp.sin(s/2)**2 < CP_INK*s*s:
        ok = False; break
check("(1b) P >= %s s^2 on |s|<=1.2" % CP_INK, ok,
      "(sharp const sin^2(0.6)/1.44 = %s)" % mp.nstr(PR/R_BALL**2, 6))

# (1c) P <= s^2/4 globally
ok = all(mp.sin(s/2)**2 <= s*s/4 + mp.mpf(10)**-35
         for s in [mp.pi*mp.mpf(k)/2000 for k in range(2001)])
check("(1c) P <= s^2/4 on [0,pi]", ok)

# (1d) on B: w >= (P+Q)(1 - (P+Q)/(4c^2)) >= 0.6812 (P+Q) at
#      c^2 >= 1/2  (PQ <= (P+Q)^2/4); and w <= P+Q
FLOOR_B = 1 - WMAX/2                   # 1 - wmax/(4c^2) at c^2 = 1/2
check("(1d) w >= %s (P+Q) on B (c^2>=1/2)" % mp.nstr(FLOOR_B, 6),
      FLOOR_B > mp.mpf('0.6811'),
      "(= 1 - wmax/2; inked 0.6811 rounded down)")
FLOOR_B_INK = mp.mpf('0.6811')

# (1e) area lemma: Area({P+Q <= u}) <= 4 pi u / sqrt(1-u) (full
#      torus, one component).  Exact: quarter-area = iint dPdQ /
#      sqrt(PQ(1-P)(1-Q)) <= (1-u)^{-1/2} iint (PQ)^{-1/2} =
#      (1-u)^{-1/2} pi u; times 4.  Numeric spot-check at u = 0.5:
ok = True
for ut in ['0.2', '0.5', '0.8']:
    u_t = mp.mpf(ut)
    # exact slicing: quarter area = int_{P<=u} 2 asin(sqrt(u-P)) ds
    smax = 2*mp.asin(mp.sqrt(u_t)) if u_t < 1 else mp.pi
    area_true = 4*mp.quad(
        lambda s: 2*mp.asin(mp.sqrt(min(max(
            u_t - mp.sin(s/2)**2, mp.mpf(0)), mp.mpf(1)))),
        [0, smax/2, smax])
    if area_true > 4*mp.pi*u_t/mp.sqrt(1-u_t):
        ok = False
    print("      area({P+Q<=%s}) true %s <= bound %s" % (ut,
          mp.nstr(area_true, 6), mp.nstr(4*mp.pi*u_t/mp.sqrt(1-u_t), 6)),
          flush=True)
check("(1e) area lemma Area({P+Q<=u}) <= 4 pi u/sqrt(1-u)", ok)
# global branch: P >= (s/pi)^2 -> Area({w<=v}) <= 4 pi^3 v (both
# components, any v): spot-check the ingredient
ok = all(mp.sin(s/2)**2 >= (s/mp.pi)**2 - mp.mpf(10)**-35
         for s in [mp.pi*mp.mpf(k)/2000 for k in range(2001)])
check("(1e') P >= (s/pi)^2 on [0,pi]", ok)

# (1f) companions (CITED, lem:companions): spot-check both sides
ok = True
for zz in [20, 25, 32, 45, 60, 90, 112, 200]:
    z = mp.mpf(zz)
    ratio = mp.besseli(1, z)*mp.sqrt(2*mp.pi*z)/mp.e**z
    lo = 1 - 3/(8*z) - mp.mpf('0.6')/z**2
    hi = 1 - 3/(8*z) + mp.mpf('0.6')/z**2
    if not (lo <= ratio <= hi):
        ok = False; break
check("(1f) two-term companions bracket I_1 on z in [20,200]", ok)

# (1f') GLOBAL upper mini-lemma (audit round 3, repair route (a)):
#   I_1(z) <= e^z/sqrt(2 pi z)  for ALL z > 0.
# PROOF (exact, one paragraph): from the lem:I1low representation
#   I_1(z) = (2 e^z/pi) int_0^1 e^{-2zu^2} (1-2u^2)/sqrt(1-u^2) du;
# the piece on [1/sqrt2, 1] is <= 0 (1-2u^2 <= 0 there); on
# [0, 1/sqrt2] the algebraic factor obeys
#   (1-2u^2)/sqrt(1-u^2) <= 1  iff  (1-2u^2)^2 <= 1-u^2
#   iff  u^2 (4u^2 - 3) <= 0  iff  u^2 <= 3/4   (true: u^2 <= 1/2);
# completing the Gaussian, (2 e^z/pi)(1/2) sqrt(pi/(2z))
#   = e^z/sqrt(2 pi z).  QED.  This is [T5]'s kernel witness on its
# FULL layer domain (z down to z_s sqrt(0.1) ~ 13.4 at the window
# corner) - the round-2 fixed-V redesign had silently extended the
# z >= 20 companion witness below its range (audit round 3).
ok = True
for k in range(1, 3001):
    z = mp.mpf(k)/100          # z in (0, 30]
    if mp.besseli(1, z) > mp.e**z/mp.sqrt(2*mp.pi*z) + mp.mpf(10)**-25:
        ok = False; break
check("(1f') global mini-lemma I_1(z) <= e^z/sqrt(2 pi z), z in "
      "(0,30] grid", ok, "(derived exactly; grid is calibration)")

# (1g) A(z) = e^{-z} I_1(z)/z <= 1/2, decreasing (CITED): spot
ok = True
prev = mp.mpf('0.5') + mp.mpf(10)**-30
for zz in range(1, 400):
    z = mp.mpf(zz)/4
    a = mp.besseli(1, z)/mp.e**z/z
    if a > prev or a > mp.mpf('0.5'):
        ok = False; break
    prev = a
check("(1g) A(z) <= 1/2 and decreasing (spot z<=100)", ok)

# (1h) mini-lemma (a) (CITED): z <= z_s on the torus for c^2>=1/2
ok = True
for c in [mp.sqrt(mp.mpf(1)/2), mp.mpf('0.85'), mp.mpf('0.99')]:
    s4 = mp.sqrt(1-c*c)
    for k in range(0, 41):
        for j in range(0, 41):
            s = mp.pi*k/40; a = mp.pi*j/40
            P = mp.sin(s/2)**2; Q = mp.sin(a/2)**2
            R2 = 4*c*c*(1-P)*(1-Q) + 4*s4*s4*P*Q
            if mp.sqrt(R2) > 2*c + mp.mpf(10)**-30:
                ok = False
check("(1h) z <= z_s on torus (c^2 >= 1/2), grid spot", ok)

# (1i) rest floor: outside B and B', g = P+Q-2PQ >= w0.
#      Case analysis (M = max(P,Q) >= PR; m = min <= 1-PR):
#      M <= 1/2: g >= M >= PR.  M > 1/2, m <= M <= 1-PR:
#      g >= 2M(1-M) >= 2(1-PR)PR.  M > 1-PR: g >= M(1-m)+m(1-M)
#      >= 1-(1-PR) = PR at m <= 1-PR (linear in M, min at M=1).
w0_sharp = min(PR, 2*PR*(1-PR))
check("(1i) rest floor w >= %s (inked %s)" % (mp.nstr(w0_sharp, 6),
      W0_INK), w0_sharp >= W0_INK,
      "min(PR, 2PR(1-PR)) with PR = %s" % mp.nstr(PR, 8))
# numeric confirmation on the rest region
ok = True
for k in range(0, 161):
    for j in range(0, 161):
        s = mp.pi*k/160; a = mp.pi*j/160
        inB = (s <= R_BALL and a <= R_BALL)
        inBp = (s >= mp.pi-R_BALL and a >= mp.pi-R_BALL)
        if inB or inBp:
            continue
        P = mp.sin(s/2)**2; Q = mp.sin(a/2)**2
        if P+Q-2*P*Q < W0_INK - mp.mpf(10)**-30:
            ok = False
check("(1i') rest floor numeric grid confirmation", ok)

# (1j) mirror chart identity: 1-w = (s4/c)^2 (1-w') exactly
ok = True
for (cc, ss, aa) in [('0.72', '2.3', '2.9'), ('0.80', '3.0', '2.2'),
                     ('0.95', '2.8', '3.1')]:
    c = mp.mpf(cc); s4 = mp.sqrt(1-c*c)
    s = mp.mpf(ss); a = mp.mpf(aa)
    P = mp.sin(s/2)**2; Q = mp.sin(a/2)**2
    w = P + Q - P*Q/c**2
    Pp = mp.cos(s/2)**2; Qp = mp.cos(a/2)**2
    wp = Pp + Qp - Pp*Qp/s4**2
    if abs((1-w) - (s4/c)**2*(1-wp)) > mp.mpf(10)**-20:
        ok = False
check("(1j) mirror chart 1-w = (s4/c)^2 (1-w')", ok)

# (1k) absorption constants by convexity (endpoint evaluation):
#      h(w) = -(3/4) ln(1-w) - 0.1*L*w is convex; max at endpoints.
def c_abs(L, wtop):
    h0 = mp.mpf(0)
    h1 = -mp.mpf(3)/4*mp.log(1-wtop) - mp.mpf('0.1')*L*wtop
    return mp.e**max(h0, h1)
CABS_B  = c_abs(BETAC_MIN, WMAX)          # main ball, beta c >= 10.6066
CABS_M  = c_abs(S4_L*BETA1, WMAX)         # mirror,   beta s4 >= 8.7
check("(1k) absorption C_abs(B) = %s <= 1.089 (ink)" %
      mp.nstr(CABS_B, 6), CABS_B <= mp.mpf('1.089'))
check("(1k') absorption C'_abs(mirror) = %s <= 1.230 (ink)" %
      mp.nstr(CABS_M, 6), CABS_M <= mp.mpf('1.230'))
CABS_B_INK = mp.mpf('1.089'); CABS_M_INK = mp.mpf('1.230')

# (1l) bracket monotonicity: f(x) = x^{-3/2}(1 - a/x - b/x^2)
#      decreasing on x in [0.6, 1] for a <= 3/(8*20), b <= 0.6/400:
#      f' = x^{-5/2}(-3/2 + (5a/2)/x + (7b/2)/x^2) < 0.
a_max = mp.mpf(3)/(8*20); b_max = mp.mpf('0.6')/400
worst = -mp.mpf(3)/2 + (5*a_max/2)/mp.mpf('0.6') \
        + (7*b_max/2)/mp.mpf('0.36')
check("(1l) prefactor bracket decreasing (worst f'-factor %s < 0)"
      % mp.nstr(worst, 4), worst < 0)

# ---------------------------------------------------------------
print("\n--- PART 2: the assembled m_low(beta, t) (derived closed "
      "form; inked constants) ---")

def m_low(beta, t, pieces=False):
    beta = mp.mpf(beta); t = mp.mpf(t)
    c = mp.cos(t/4); s4 = mp.sin(t/4)
    zs = 4*beta*c; bc = beta*c
    d4 = c - s4
    # T1
    br1 = 1 - 3/(8*zs) - mp.mpf('0.6')/zs**2
    br2 = 1 - mp.e**(-bc*R_BALL**2/2) - 3/(8*bc)
    T1 = 2*(mp.sqrt(2*mp.pi)/4)/c**mp.mpf('2.5')*br1*br2**2
    # T2
    lam_eff = CP_INK*mp.mpf('1.9')*FLOOR_B_INK*bc   # rate in s^2
    GB = (beta/(4*mp.sqrt(2*mp.pi))/c**mp.mpf('1.5'))*CABS_B_INK \
         * (mp.pi/4)/lam_eff**2
    T2 = -2*GB
    # T3 (zones)
    if s4 >= S4_L:
        q4 = WMAX/(4*s4*s4)
        lamp = CP_INK*mp.mpf('1.9')*(1-q4)*beta*s4
        MIR = (beta/(4*mp.sqrt(2*mp.pi))/s4**mp.mpf('1.5'))*CABS_M_INK \
              * mp.pi/lamp * mp.e**(-4*beta*d4)
    elif s4 >= S4_C:
        MIR = 4*R_BALL**2*beta**mp.mpf('2.5')*mp.e**(-4*beta*d4)
    else:
        dfar = c - mp.sqrt(c*c*PR**2 + s4*s4)
        MIR = 4*R_BALL**2*beta**mp.mpf('2.5')*mp.e**(-4*beta*dfar)
    T3 = -2*MIR
    # T5 (Abel-corrected layered rest; audit round 2)
    pref = beta/(4*mp.sqrt(2*mp.pi))/c**mp.mpf('1.5')
    def Abar_r(v):
        # min of the two valid branches (external audit on 0794fb3:
        # true crossover (1-16/pi^4)/2 = 0.4178721..., not 0.418;
        # min form valid, nondecreasing, grid-identical)
        b = 4*mp.pi**3*v
        if v < mp.mpf('0.5'):
            a = 16*mp.pi*v/mp.sqrt(1-2*v)
            if a < b:
                return a - mp.mpf('4.006')
        return b - mp.mpf('4.006')
    def phi(v):
        return (1-v)**mp.mpf('-0.75')*mp.e**(-2*bc*v)
    v0 = W0_INK; dv = mp.mpf(1)/50; V = mp.mpf('0.9')
    v = v0 + dv
    S = phi(v0)*Abar_r(v)
    while v < V - mp.mpf('1e-12'):
        v2 = min(v+dv, V)
        S += phi(v)*(Abar_r(v2)-Abar_r(v))
        v = v2
    REST = pref*S + (2*mp.pi)**2*beta**mp.mpf('2.5') \
        * mp.e**(-(1-mp.sqrt(mp.mpf('0.1')))*zs)
    T5 = -2*REST
    out = T1 + T2 + T3 + T5
    if pieces:
        return out, (T1, T2, T3, T5)
    return out

# headline evaluations
for (tt, bb) in [(0.5, 15), (1.5, 15), (2.0, 15), (2.5, 15),
                 (2.9, 15), (3.0416, 15)]:
    v, pc = m_low(bb, tt, pieces=True)
    print("  m_low(%g, t=%g) = %s   [T1 %s | T2 %s | T3 %s | T5 %s]"
          % (bb, tt, mp.nstr(v, 6), mp.nstr(pc[0], 5),
             mp.nstr(pc[1], 4), mp.nstr(pc[2], 4), mp.nstr(pc[3], 4)),
          flush=True)

# ---------------------------------------------------------------
print("\n--- PART 3: the floor m_low >= 1/2 on the whole window ---")

# beta-monotonicity witnesses (each piece nondecreasing in beta at
# fixed t, beta >= 15): T1 brackets increase; |T2| ~ 1/beta;
# |T3| ~ e^{-4 beta d4} (d4>0) resp. beta^{5/2}e^{-4 beta d}, d >=
# 0.2346 > 2.5/(4*15); |T5| layer terms beta e^{-2 beta c v_k},
# v_k >= 0.318 > 1/(2*15*c) and shard beta^{5/2}e^{-4 beta c + 20}.
ok = True
for tt in ['0.3', '1.5', '2.5', '2.9', '3.04']:
    t = mp.mpf(tt)
    prev = None
    for bb in [15, 18, 25, 40, 80, 200, 1000]:
        if mp.pi - t < CWIN/bb:
            continue
        v = m_low(bb, t)
        if prev is not None and v < prev - mp.mpf(10)**-12:
            ok = False
            print("  monotonicity VIOLATION t=%s beta=%s" % (tt, bb))
        prev = v
check("(3a) beta-monotonicity numeric confirmation (5 t's)", ok)

# the 1D sweep along beta_min(t) = max(15, CWIN/(pi-t))
t0 = time.time()
worst_v = mp.mpf(10); worst_t = None
NGRID = 12000
for k in range(1, NGRID+1):
    t = mp.pi*mp.mpf(k)/(NGRID+1)
    bmin = max(BETA1, CWIN/(mp.pi-t))
    if mp.pi - t < CWIN/bmin - mp.mpf(10)**-25:
        continue
    v = m_low(bmin, t)
    if v < worst_v:
        worst_v = v; worst_t = t
print("  sweep: %d points, min m_low = %s at t = %s (%.0fs)"
      % (NGRID, mp.nstr(worst_v, 8), mp.nstr(worst_t, 8),
         time.time()-t0), flush=True)
check("(3b) m_low >= 0.5 + 0.05 grid margin on the sweep",
      worst_v >= mp.mpf('0.55'),
      "(continuity: all pieces are C^1 in t with O(10) derivatives; "
      "grid step %s)" % mp.nstr(mp.pi/NGRID, 3))

# ---------------------------------------------------------------
print("\n--- PART 4: bench vs truth (verified numerics, "
      "calibration only) ---")

def truth_pieces(beta, t):
    """m-normalized quadratures of the exact integrand, by region.
    One pass per region; weights 1, P+Q, D accumulated together via
    three quadratures of a shared kernel closure (design bench)."""
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
    ONE = lambda k, P, Q: k
    PQW = lambda k, P, Q: k*(P+Q)
    DW  = lambda k, P, Q: k*2*(1-P-Q)
    r = R_BALL
    Bx = ([0, r/2, r], [0, r/2, r])
    Mx = ([mp.pi-r, mp.pi-r/2, mp.pi], [mp.pi-r, mp.pi-r/2, mp.pi])
    # ordered nodes (external audit on 7225d4e: pi - r < 2 made
    # the old [r, 2, pi-r] lists non-monotone; split at pi/2)
    hp = mp.pi/2
    RESTS = [([r, 2, mp.pi], [0, r]), ([0, r], [r, 2, mp.pi]),
             ([r, hp, mp.pi-r], [r, hp, mp.pi-r]),
             ([mp.pi-r, mp.pi], [r, hp, mp.pi-r]),
             ([r, hp, mp.pi-r], [mp.pi-r, mp.pi])]
    B_K   = wq(ONE, *Bx); B_KPQ = wq(PQW, *Bx); B_KD = wq(DW, *Bx)
    M_K   = wq(ONE, *Mx); M_KD  = wq(DW, *Mx)
    rest = sum(wq(ONE, *xy) for xy in RESTS)
    rest_KD = sum(wq(DW, *xy) for xy in RESTS)
    m_true = B_KD + M_KD + rest_KD
    return B_K, B_KPQ, B_KD, M_K, rest, m_true

BENCH = [(0.5, 15), (1.5, 15), (2.5, 15), (2.9, 15), (3.0416, 15),
         (1.5, 30), (3.1, 36.05)]
print("  cell            m_low    m_true   ratio  | piece slacks "
      "(mu1 / GB / mirror / rest)", flush=True)
allok = True
mp_bench_dps = 15
for (tt, bb) in BENCH:
    t0 = time.time()
    v, pc = m_low(bb, tt, pieces=True)
    mp.mp.dps = mp_bench_dps
    B_K, B_KPQ, B_KD, M_K, rest, m_true = truth_pieces(bb, tt)
    mp.mp.dps = 25
    T1, T2, T3, T5 = pc
    s_mu1 = B_K/(T1/2)
    s_gb  = (-T2/2)/B_KPQ if B_KPQ > 0 else mp.inf
    s_mir = (-T3/2)/M_K if (M_K > 0 and T3 < 0) else mp.inf
    s_rest = (-T5/2)/rest if rest > 0 else mp.inf
    okc = (v <= m_true) and (T1/2 <= B_K) and (-T2/2 >= B_KPQ) \
          and (-T3/2 >= M_K) and (-T5/2 >= rest)
    allok = allok and okc
    print("  (%.4g,%.4g)  %s  %s  %s | %s / %s / %s / %s  %s (%.0fs)"
          % (tt, bb, mp.nstr(v, 5), mp.nstr(m_true, 5),
             mp.nstr(m_true/v, 4), mp.nstr(s_mu1, 4), mp.nstr(s_gb, 4),
             mp.nstr(s_mir, 3), mp.nstr(s_rest, 3),
             "OK" if okc else "DOMINANCE FAIL", time.time()-t0),
          flush=True)
check("(4) every piece dominates its truth and m_low <= m_true "
      "at all bench cells", allok)

# ---------------------------------------------------------------
n_ok = sum(1 for x in PASS if x)
print("\n=== CASCADE 1 fabrication: %d/%d checks PASS ==="
      % (n_ok, len(PASS)))
print("VERDICT: %s" % ("ALL PASS - ready for independent audit"
                       if all(PASS) else "MEASURED FAILURE - commit "
                       "with diagnosis"), flush=True)
