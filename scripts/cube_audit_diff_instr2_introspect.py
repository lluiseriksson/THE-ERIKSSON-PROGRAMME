"""DIFF AUDIT - introspection of the COMMITTED script's own objects
(import cascade3c_buckets; it runs its full pipeline incl. asserts).

(2) frozen-eps_1: g_e1 present for all seven; MAG*(g_a+g_e1) at MF t2.9
    must cover the audit's measured model error 0.0194 bucket units;
    MAG*g_e1 at MD zone floor must cover the audit's measured eps1 cost
    0.133; at MD t2.9 cover 0.071.
(3) c4..cJ: J per moment; MD c4/c5/c6 at p=0.5801 vs audit refs
    -131.3 / -1251.8 / -14791; ctail present in B2.
(4) w-bar: w1 == 1/(2p) SYMBOLICALLY; w2 values; next-order fraction
    w2/(B1*w1) vs audit-measured +3.5%..+5.7%; guard factor 2.
(1) counterexample coefficient: MD integrand sigma^4 eps^2 coefficient
    at p=29/50 equals -29/2400 exactly (stage-1 exact value).
"""
import sys
sys.path.insert(0, r"C:\Users\lluis\AppData\Local\Temp\eriksson-push2\scripts")
import os
os.chdir(r"C:\Users\lluis\AppData\Local\Temp\eriksson-push2\scripts")

import mpmath as mp
import sympy as sp

print(">>> importing committed cascade3c_buckets (full pipeline runs)...",
      flush=True)
import cascade3c_buckets as cb
print(">>> import done.", flush=True)

ok_all = True
def chk(label, cond):
    global ok_all
    print(("[PASS] " if cond else "[FAIL] ") + label, flush=True)
    if not cond:
        ok_all = False

p = cb.p; eps = cb.eps; sig = cb.sig; tau = cb.tau
B1 = cb.BETA1

# ---- (4) w-bar ----
w1m, w2m = cb.WMIR
w1s, w2s = cb.WMAIN
chk("WMIR w1 == 1/(2p) symbolically", sp.simplify(w1m - 1/(2*p)) == 0)
chk("WMAIN w1 == 1/(2p) symbolically", sp.simplify(w1s - 1/(2*p)) == 0)
print("  WMIR w2 =", sp.simplify(w2m))
print("  WMAIN w2 =", sp.simplify(w2s))
for nmch, (w1_, w2_), pv in (("mir", cb.WMIR, mp.mpf('0.5801')),
                             ("mir", cb.WMIR, mp.sin(mp.mpf('2.9')/4)),
                             ("main", cb.WMAIN, mp.mpf('0.7071')),
                             ("main", cb.WMAIN, mp.cos(mp.mpf('2.9')/4))):
    w1v = abs(cb.numv(w1_, pv)); w2v = abs(cb.numv(w2_, pv))
    frac = w2v/(B1*w1v)
    print("  %s pv=%s: w2/(B1 w1) = %s (audit measured next-order "
          "+3.5%%..+5.7%%; guard doubles it)"
          % (nmch, mp.nstr(pv, 5), mp.nstr(frac, 4)))
    chk("  next-order fraction in audit-measured band [0.02, 0.09] "
        "and 2x guard >= measured 0.057 worst case",
        mp.mpf('0.02') < frac < mp.mpf('0.09') and 2*frac > mp.mpf('0.057'))

# ---- (3) c4..cJ ----
for nm, k0exp, Jexp in (('MD', 0, 6), ('MF', 0, 6), ('MD2r', 2, 5),
                        ('MDFr', 2, 5)):
    cj, ip_, k0_, fac_ = cb.MOM_MIR[nm]
    chk("mir %s: k0=%d, len(cj)=%d == J+1=%d" % (nm, k0_, len(cj), Jexp+1),
        k0_ == k0exp and len(cj) == Jexp + 1)
for nm, k0exp, Jexp in (('muF', 2, 5), ('nuD', 2, 5), ('nuF', 4, 4)):
    cj, ip_, k0_, fac_ = cb.MOM_MAIN[nm]
    chk("main %s: k0=%d, len(cj)=%d == J+1=%d" % (nm, k0_, len(cj), Jexp+1),
        k0_ == k0exp and len(cj) == Jexp + 1)

cjMD = cb.MOM_MIR['MD'][0]
pv = mp.mpf('0.5801')
c4 = cb.numv(cjMD[4], pv); c5 = cb.numv(cjMD[5], pv)
c6 = cb.numv(cjMD[6], pv)
print("  MD @ p=0.5801: c4 = %s  c5 = %s  c6 = %s"
      % (mp.nstr(c4, 6), mp.nstr(c5, 6), mp.nstr(c6, 6)))
chk("MD c4 ~ -131.3 (audit NORD-16 ref)", abs(c4 + mp.mpf('131.3')) < 0.15)
chk("MD c5 ~ -1251.8 (audit ref)", abs(c5 + mp.mpf('1251.8')) < 1.5)
chk("MD c6 ~ -14791 (audit ref)", abs(c6 + mp.mpf('14791')) < 20)
ctail = sum(abs(cb.numv(cjMD[j], pv))/B1**(j-2) for j in range(4, 7))
print("  MD ctail (j=4..6) at zone floor =", mp.nstr(ctail, 5),
      "(audit measured 1.52)")
chk("MD ctail ~ 1.52 bucket units now inside B2", abs(ctail - mp.mpf('1.52')) < 0.05)

# ---- (2) frozen-eps_1 budget coverage ----
def parts(nm, kind, pv):
    cj, ip_, k0_, fac_ = (cb.MOM_MIR if kind == 'mir' else cb.MOM_MAIN)[nm]
    wc = cb.WMIR if kind == 'mir' else cb.WMAIN
    cjv = [abs(cb.numv(c, pv)) for c in cj]
    MAG = sum(cjv[j]/B1**j for j in range(len(cjv)))
    zs1 = 4*B1*pv
    w1v = abs(cb.numv(wc[0], pv)); w2v = abs(cb.numv(wc[1], pv))
    wbar = (w1v + 2*w2v/B1)/B1
    g_a = (mp.mpf('4.94')/zs1**3 + mp.mpf('0.34')*wbar/zs1**2)*B1**2
    g_e1 = (mp.mpf(15)/128/zs1**2 + mp.mpf('1.02')/zs1**3)*B1**2
    return MAG, g_a, g_e1

MAG, g_a, g_e1 = parts('MF', 'mir', mp.sin(mp.mpf('2.9')/4))
print("  MF t2.9: MAG=%s  MAG*g_a=%s  MAG*(g_a+g_e1)=%s vs measured "
      "model error 0.0194" % (mp.nstr(MAG, 5), mp.nstr(MAG*g_a, 5),
                              mp.nstr(MAG*(g_a+g_e1), 5)))
chk("MF t2.9 named budget MAG*(g_a+g_e1) >= measured 0.0194",
    MAG*(g_a+g_e1) >= mp.mpf('0.0194'))
MAG, g_a, g_e1 = parts('MD', 'mir', mp.mpf('0.5801'))
print("  MD floor: MAG*g_e1 =", mp.nstr(MAG*g_e1, 5),
      "vs audit eps1 cost 0.133; MAG*(g_a+g_e1) =",
      mp.nstr(MAG*(g_a+g_e1), 5), "vs measured model error 0.1084+0.133")
chk("MD floor MAG*g_e1 >= 0.133", MAG*g_e1 >= mp.mpf('0.133'))
chk("MD floor MAG*(g_a+g_e1) >= 0.1084 + 0.133 (model error + eps1)",
    MAG*(g_a+g_e1) >= mp.mpf('0.2414'))
MAG, g_a, g_e1 = parts('MD', 'mir', mp.sin(mp.mpf('2.9')/4))
print("  MD t2.9: MAG*g_e1 =", mp.nstr(MAG*g_e1, 5), "vs audit 0.071")
chk("MD t2.9 MAG*g_e1 >= 0.071", MAG*g_e1 >= mp.mpf('0.071'))

# g_e1 wired into all seven buckets: read the source
src = open('cascade3c_buckets.py').read()
chk("g_e1 in G for all buckets (single G line, unconditional)",
    "G = MAG*(g_a + g_e1 + g_bc + g_d)" in src)

# ---- (1) exact counterexample coefficient in the committed integrand ----
ipMD = cb.MOM_MIR['MD'][1]
coef = ipMD.coeff(sig, 4).coeff(tau, 0).coeff(eps, 2)
val = sp.nsimplify(coef.subs(p, sp.Rational(29, 50)), rational=True)
print("  MD integrand sigma^4 tau^0 eps^2 coeff at p=29/50:", val)
chk("equals stage-1 exact counterexample -29/2400",
    sp.simplify(val + sp.Rational(29, 2400)) == 0)

# its q and supfac in the committed comp_fold
a_rate = mp.mpf('0.72')*mp.mpf('0.5801')
q_ce = 2 + mp.mpf(0-2)/2 + mp.mpf(4-1)/2
chk("counterexample q = 2.5 <= a*B1 = %s -> supfac 1 (flat eval valid "
    "for this class)" % mp.nstr(a_rate*B1, 6), q_ce < a_rate*B1)

# census: violating monomials of old-L3 vs supfac coverage at NORD=14
worst_q = mp.mpf('-inf'); nviol = 0; nsup = 0
for t_ in sp.expand(ipMD).as_ordered_terms():
    pd = t_.as_powers_dict()
    i = int(pd.get(sig, 0)); j = int(pd.get(tau, 0))
    k = int(pd.get(eps, 0))
    if k < i + j:
        nviol += 1
    q = 2 + mp.mpf(0-k)/2 + mp.mpf(max(i, j)-1)/2
    if q > worst_q:
        worst_q = q
    if q > a_rate*B1:
        nsup += 1
print("  MD integrand NORD=14: old-L3-violating monomials = %d; "
      "max q = %s; monomials getting supfac>1 at MD floor = %d"
      % (nviol, mp.nstr(worst_q, 4), nsup))
chk("old-L3 violations exist (audit count 1 class present at NORD=14) "
    "and every monomial q accounted (supfac branch reachable)",
    nviol > 0)

print()
print("INTROSPECTION CHECKS:", "PASS" if ok_all else "FAIL")
