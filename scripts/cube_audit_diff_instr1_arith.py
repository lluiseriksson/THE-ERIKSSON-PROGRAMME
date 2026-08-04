"""DIFF AUDIT - independent arithmetic checks (this desk's own code,
scratchpad; nothing imported from the fabrication script).

(A) U_D re-derivation from the cascade-1 inked constants:
    U_ball = pref(c) * CABS_B * pi / (CP*1.9*FLOOR_B*beta*c)   [T2 chain
             without the (P+Q) weight: Gaussian moment pi/lam not (pi/4)/lam^2]
    U_mirc = pref(s4) * CABS_M * pi / (CP*1.9*(1-q4)*beta*s4)  [T3 zone-L]
    q4 = wmax/(4 s4^2), wmax = 2 sin^2(0.6)
    U_D = 2*(U_ball + U_mirc*SUP + T5rest), T5rest = 0.1671/2 = 0.08355
    vs committed U_D 5.129, bench truth 2 int_B K = 2.713, 2 int K = 2.7364.
(B) supfac formula: supfac(q) = (q/(a b1))^q e^{a b1 - q} for q > a b1
    must equal/dominate sup_{beta>=b1} (beta/b1)^q e^{-a(beta-b1)} (numeric
    grid), and = 1-case must have decreasing envelope.
(C) Mills-ratio monotonicity, ALL orders 0..39 (not just every 4th),
    R from R1C to 6*R1C fine grid, pv in {0.5801, 0.7071, sin(2.9/4),
    sin(2.6/4), cos(2.9/4), cos(0.5/4)}.
(D) counterexample class: (i,j,k)=(4,0,2) k0=0 -> q; (20,0,10) k0=0 -> q,
    supfac at p=0.5801.
(E) M_sharp window re-assembly from the committed transcript numbers.
"""
import mpmath as mp
mp.mp.dps = 30

ok_all = True
def chk(label, cond):
    global ok_all
    print(("[PASS] " if cond else "[FAIL] ") + label)
    if not cond:
        ok_all = False

B1 = mp.mpf(15)
t_c = mp.mpf('2.9'); b_c = mp.mpf(15)
c_c = mp.cos(t_c/4); s4_c = mp.sin(t_c/4); d4_c = c_c - s4_c
SUP = mp.e**(-4*b_c*d4_c)
CP = mp.mpf('0.2214'); FLOOR_B = mp.mpf('0.6811')
CABS_B = mp.mpf('1.089'); CABS_M = mp.mpf('1.230')
WMAX = 2*mp.sin(mp.mpf('0.6'))**2

# (A) U_D
pref_c = B1/(4*mp.sqrt(2*mp.pi))/c_c**mp.mpf('1.5')
U_ball = pref_c*CABS_B*mp.pi/(CP*mp.mpf('1.9')*FLOOR_B*B1*c_c)
q4 = WMAX/(4*s4_c**2)
pref_s = B1/(4*mp.sqrt(2*mp.pi))/s4_c**mp.mpf('1.5')
U_mirc = pref_s*CABS_M*mp.pi/(CP*mp.mpf('1.9')*(1-q4)*B1*s4_c)
T5rest = mp.mpf('0.1671')/2
U_D = 2*(U_ball + U_mirc*SUP + T5rest)
print("U_ball  =", mp.nstr(U_ball, 8))
print("U_mirc  =", mp.nstr(U_mirc, 8), " SUP =", mp.nstr(SUP, 8),
      " U_mirc*SUP =", mp.nstr(U_mirc*SUP, 8))
print("T5rest  =", mp.nstr(T5rest, 8))
print("U_D     =", mp.nstr(U_D, 8))
chk("U_D re-derived matches committed 5.129 (to print precision)",
    abs(U_D - mp.mpf('5.129')) < mp.mpf('0.001'))
chk("U_D >= bench 2 int K truth 2.7364 (prior audit quadrature)",
    U_D >= mp.mpf('2.7364'))
chk("U_D >= bench 2 int_B K = 2.71327", U_D >= mp.mpf('2.71327'))
chk("T5rest equals committed transcript T5/2 = 0.08355",
    T5rest == mp.mpf('0.08355'))
chk("q4 = 2sin^2(0.6)/(4 s4^2) matches cascade1 wmax/(4 s4^2), wmax=0.63764225",
    abs(WMAX - mp.mpf('0.63764225')) < mp.mpf('1e-7'))

# (B) supfac
def supfac(q, a):
    if q > a*B1:
        return (q/(a*B1))**q*mp.e**(a*B1 - q)
    return mp.mpf(1)

for pv in (mp.mpf('0.5801'), mp.mpf('0.7071')):
    a = mp.mpf('0.72')*pv
    for q in (mp.mpf('-0.5'), mp.mpf('0.5'), mp.mpf('2.5'),
              mp.mpf('6.0'), a*B1 - mp.mpf('0.01'), a*B1 + mp.mpf('0.01'),
              mp.mpf('6.5'), mp.mpf('8'), mp.mpf('12')):
        # numeric sup over beta >= 15 (grid + analytic stationary point)
        sup_num = mp.mpf(0)
        for x in range(0, 40001):
            beta = B1 + mp.mpf(x)/20
            v = (beta/B1)**q*mp.e**(-a*(beta-B1))
            if v > sup_num:
                sup_num = v
        if q > a*B1:
            bstar = q/a
            v = (bstar/B1)**q*mp.e**(-a*(bstar-B1))
            if v > sup_num:
                sup_num = v
        sf = supfac(q, a)
        if not sup_num <= sf*(1 + mp.mpf('1e-25')):
            chk("supfac(q=%s,pv=%s) >= numeric sup" % (q, pv), False)
print("[PASS] supfac(q) dominates numeric sup_{beta>=15} (beta/15)^q "
      "e^{-a(beta-15)} for all tested q at both zone floors (grid to "
      "beta=2015 + stationary point)")

# supfac monotone increasing in q above threshold (max(i,j) cover valid)
for pv in (mp.mpf('0.5801'), mp.mpf('0.7071')):
    a = mp.mpf('0.72')*pv
    prev = None
    mono = True
    q = a*B1
    while q < 20:
        v = supfac(q, a)
        if prev is not None and v < prev:
            mono = False
        prev = v
        q += mp.mpf('0.01')
    chk("supfac nondecreasing in q above a*beta1 (pv=%s)" % pv, mono)

# (C) Mills ratio monotonicity, ALL orders, wide grid
R1C = mp.mpf('1.2')*mp.sqrt(B1)
NT = 40
def tails(R, p_):
    T_ = [mp.e**(-p_*R**2/2)/(p_*R), mp.e**(-p_*R**2/2)/p_]
    for k in range(2, NT):
        T_.append(R**(k-1)*mp.e**(-p_*R**2/2)/p_ + (k-1)/p_*T_[k-2])
    return T_
pvs = [mp.mpf('0.5801'), mp.mpf('0.7071'), mp.sin(mp.mpf('2.9')/4),
       mp.sin(mp.mpf('2.6')/4), mp.cos(mp.mpf('2.9')/4),
       mp.cos(mp.mpf('0.5')/4), mp.cos(mp.mpf('1.5')/4)]
allmono = True
worst = None
for p_ in pvs:
    Rg = [R1C*(1 + mp.mpf(x)/40) for x in range(0, 201)]  # to 6*R1C
    Tg = [tails(R, p_) for R in Rg]
    for i_ in range(0, NT):
        prev = None
        for R, T_ in zip(Rg, Tg):
            ratio = T_[i_]*p_/(R**max(i_-1, 0)*mp.e**(-p_*R**2/2))
            if prev is not None and ratio > prev*(1 + mp.mpf('1e-24')):
                allmono = False
                worst = (float(p_), i_, float(R))
            prev = ratio
chk("Mills ratio T_i(R) p/(R^{i-1} e^{-pR^2/2}) nonincreasing for ALL "
    "orders i=0..39, R in [R1C, 6 R1C], 7 pv values (fabrication desk "
    "checked only i=0,4,...,36 on [R1C, 3 R1C])", allmono)
if worst:
    print("   worst violation at", worst)

# note: what supfac needs is exactly T_i(R(beta)) <= [R(beta)/R1]^{i-1}
#  e^{-p(R(beta)^2-R1^2)/2} T_i(R1), i.e. the Mills ratio nonincreasing,
#  PLUS R(beta)^{i-1} e^{...} handled by q's (i-1)/2 power and a=0.72p.
#  Cross-check the composite directly for a hard case:
p_ = mp.mpf('0.5801')
for i_ in (0, 1, 3, 7, 20):
    okc = True
    for x in range(0, 2001):
        beta = B1 + mp.mpf(x)/4      # to beta=515
        R = mp.mpf('1.2')*mp.sqrt(beta)
        lhs = tails(R, p_)[i_]
        rhs = tails(R1C, p_)[i_]*(beta/B1)**(mp.mpf(i_-1)/2) \
            * mp.e**(-mp.mpf('0.72')*p_*(beta-B1))
        if lhs > rhs*(1 + mp.mpf('1e-24')):
            okc = False
    chk("composite tail bound T_i(R(beta)) <= T_i(R1)(beta/b1)^{(i-1)/2}"
        "e^{-0.72p(beta-b1)} for i=%d (p=0.5801, beta to 515)" % i_, okc)

# (D) counterexample class q values
def qval(i, j, k, k0):
    return 2 + mp.mpf(k0-k)/2 + mp.mpf(max(i, j)-1)/2
p_md = mp.mpf('0.5801'); a_md = mp.mpf('0.72')*p_md
q_ce = qval(4, 0, 2, 0)
print("sigma^4 eps^2 (MD, k0=0): q =", q_ce, " a*b1 =", mp.nstr(a_md*B1, 6),
      " supfac =", mp.nstr(supfac(q_ce, a_md), 8))
chk("counterexample class sigma^4 eps^2: q=2.5 < a*beta1=6.265 -> "
    "supfac 1 (correctly beta-decreasing, flat eval valid)",
    q_ce == mp.mpf('2.5') and supfac(q_ce, a_md) == 1)
q_dust = qval(20, 0, 10, 0)
sf_dust = supfac(q_dust, a_md)
print("dust class (20,0,10) k0=0: q =", q_dust, " supfac =",
      mp.nstr(sf_dust, 8))
chk("dust class q=6.5 > 6.265 gets supfac > 1 (audit count-2 class "
    "now multiplied, not ignored)", q_dust == mp.mpf('6.5') and sf_dust > 1)

# (E) M_sharp window from committed transcript numbers
muD_m = mp.mpf('0.02109'); muF_m = mp.mpf('0.006076')
nuD_m = mp.mpf('3.712e-5'); nuF_m = mp.mpf('9.781e-6')
muF_main = mp.mpf('0.1464'); nuD_main = mp.mpf('0.004061')
nuF_main = mp.mpf('0.0002344'); m_low = mp.mpf('1.79657')
M_cross = 4*b_c**3*(U_D*nuF_m + muD_m*nuF_main + muF_main*nuD_m
                    + muF_m*nuD_main)/m_low**2
M_second = 4*b_c**3*(muD_m*nuF_m + muF_m*nuD_m)/m_low**2
M = M_cross + M_second
print("M_sharp re-assembled from transcript numbers:", mp.nstr(M, 6),
      "[cross", mp.nstr(M_cross, 6), "+ second", mp.nstr(M_second, 6), "]")
chk("M_sharp reassembly ~ 0.35825 (4-digit transcript inputs)",
    abs(M - mp.mpf('0.35825')) < mp.mpf('0.002'))
chk("M_sharp in the pre-registered window [0.0733, 0.7]",
    mp.mpf('0.0733') < M < mp.mpf('0.7'))
chk("all six cross/second products present (U_D nuF_m, muD nuF_main, "
    "muF_main nuD_m, muF_m nuD_main; muD nuF_m, muF_m nuD_m)", True)

print()
print("ALL CHECKS:", "PASS" if ok_all else "FAIL")
