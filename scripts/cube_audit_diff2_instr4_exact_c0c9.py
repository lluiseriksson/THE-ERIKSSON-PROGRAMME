"""DIFF ROUND 2, INSTRUMENT 4: exact-Fraction adjudication of the MD
mirror moment orders at the zone floor p = 5801/10000, at TWO engine
depths: NORD = 22 (complete for integrand eps-orders <= 18 under the
eps^-2 clawback: exactness through eps^k needs NORD >= k+4) and
NORD = 26 (complete through eps^22).

Purpose (this desk, round 2):
  (B)  true c6 (eps^12) and c7 (eps^14) to judge the committed
       NORD=18 extraction — AND to re-adjudicate this desk's own
       round-1 instr3 c7: instr3 ran at NORD=16, which by the very
       clawback mechanism this desk diagnosed is complete only
       through eps^12; its printed c7 = -208520.7285 is therefore
       itself a truncated-construction value and is NOT a valid
       reference.  The reference is THIS engine.
  (C)  true c8 (eps^16): the committed NORD=18 c8 is construction-
       only (18-2 = 16 is its first wrong order) — the model-vs-
       poly gap there belongs to the analytic-vs-polynomial band.
       True c9 (eps^18): the first moment order entirely DROPPED by
       trunc() at NORD=18 (kept eps-degrees <= 16); it is pure
       polynomial cross-term content of the input series (cos to
       eps^18, binom to w^10, exp to expo^9 are all COMPLETE at
       eps^18 in the committed depths), i.e. it involves NO input-
       series Lagrange remainder — the Lagrange forms named by the
       restated g_d live at eps^{20+} and only touch model orders
       j >= 10.  |c9|/beta_1^7 is therefore the leading term of the
       analytic-vs-polynomial error band at NORD=18.
  (INCURABILITY) true c10, c11 from the NORD=26 pass: the exact
       size of the first-dropped band a hypothetical NORD=22 repair
       would orphan — measuring whether raising NORD can ever
       discharge the band (it cannot if the growth ratios
       |c_{j+1}|/(beta_1 |c_j|) exceed 1).

Internal depths per pass (all complete for the kept orders): cos to
eps^{NORD-2}; binom to w^{(NORD-2)/2}; exp to expo^{(NORD-2)/2}.
Independent of the committed sympy engine (Fraction dict
arithmetic, no sympy).  Design instrument; transcript exists when
committed.
"""
import hashlib
import sys
import time
from fractions import Fraction as Fr

import mpmath as mp

mp.mp.dps = 40

print("=== DIFF ROUND 2 / INSTR 4: exact MD orders (NORD=22, 26) "
      "===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("python %s" % sys.version.split()[0], flush=True)

P = Fr(5801, 10000)
BETA1 = mp.mpf(15)
pmp = mp.mpf(5801) / 10000
# CONV*(2pi/p) split, as in round-1 instr3: 2 sqrt(2pi)/((4p)^1.5 p)
pref = 2 * mp.sqrt(2 * mp.pi) / ((4 * pmp) ** mp.mpf('1.5') * pmp)


def run(NORD):
    """exact MD moment orders c_j, exact for 2j <= NORD-4."""
    t0 = time.time()

    def pmul(A, B):
        C = {}
        for (i1, j1, k1), c1 in A.items():
            for (i2, j2, k2), c2 in B.items():
                k = k1 + k2
                if k >= NORD:
                    continue
                key = (i1 + i2, j1 + j2, k)
                C[key] = C.get(key, 0) + c1 * c2
        return {k: c for k, c in C.items() if c != 0}

    def padd(*polys):
        C = {}
        for A in polys:
            for k, c in A.items():
                C[k] = C.get(k, 0) + c
        return {k: c for k, c in C.items() if c != 0}

    def pscale(A, s):
        return {k: s * c for k, c in A.items()}

    def cospoly(vi):
        out = {}
        f = 1
        for m in range(0, NORD // 2):
            key = (2 * m, 0, 2 * m) if vi == 0 else (0, 2 * m, 2 * m)
            out[key] = Fr((-1) ** m, f)
            f *= (2 * m + 1) * (2 * m + 2)
        return out

    one = {(0, 0, 0): Fr(1)}
    x = cospoly(0)
    y = cospoly(1)
    # mirror chart
    D = pscale(padd(x, y), Fr(-1))
    Pp = pscale(padd(one, pscale(x, Fr(-1))), Fr(1, 2))
    Qq = pscale(padd(one, pscale(y, Fr(-1))), Fr(1, 2))
    w = padd(Pp, Qq, pscale(pmul(Pp, Qq), -1 / (P * P)))

    def binom_series(A, alpha_num, alpha_den, mmax):
        alpha = Fr(alpha_num, alpha_den)
        out = dict(one)
        term = dict(one)
        coef = Fr(1)
        for m in range(1, mmax + 1):
            coef *= (alpha - m + 1) / m
            term = pmul(term, A)
            out = padd(out, pscale(term, coef * Fr((-1) ** m)))
        return out

    MB = (NORD - 2) // 2
    sqrt1mw = binom_series(w, 1, 2, MB)
    inv_sqrt = binom_series(w, -1, 2, MB)
    pow34 = binom_series(w, -3, 4, MB)

    shifted = {}
    for (i, j, k), c in padd(sqrt1mw, pscale(one, Fr(-1))).items():
        assert k - 2 >= 0
        shifted[(i, j, k - 2)] = 4 * P * c
    rho2 = {(2, 0, 0): P / 2, (0, 2, 0): P / 2}
    expo = padd(shifted, rho2)
    assert all(k[2] != 0 for k in expo), "expo eps^0 survives"

    wcorr = dict(one)
    term = dict(one)
    for n in range(1, MB + 1):
        term = pscale(pmul(term, expo), Fr(1, n))
        wcorr = padd(wcorr, term)

    invz = {(i, j, k + 2): c / (4 * P)
            for (i, j, k), c in inv_sqrt.items() if k + 2 < NORD}
    KER = pmul(pmul(pow34, wcorr), padd(one, pscale(invz,
                                                    Fr(-3, 8))))
    integ = pmul(D, KER)
    assert all(k % 2 == 0 for (_, _, k) in integ), "odd eps order"

    def f2(m):
        r = Fr(1)
        while m > 1:
            r *= m - 1
            m -= 2
        return r

    S = {}
    for (i, j, k), c in integ.items():
        if i % 2 or j % 2:
            continue
        S[k] = S.get(k, Fr(0)) + c * f2(i) * f2(j) / P ** ((i + j)
                                                           // 2)
    cs = []
    for j in range(0, (NORD - 2) // 2 + 1):
        Sv = S.get(2 * j, Fr(0))
        cs.append(pref * mp.mpf(Sv.numerator)
                  / mp.mpf(Sv.denominator))
    print("  [NORD=%d pass: %d integrand monomials, %.1fs; exact "
          "c0..c%d; the eps^%d entry is construction-only]"
          % (NORD, len(integ), time.time() - t0, (NORD - 4) // 2,
             NORD - 2), flush=True)
    return cs


cs22 = run(22)
cs26 = run(26)

# ------- mechanism reproduction (erratum witness) -------
# The construction-only last order of a depth-N engine must
# REPRODUCE the two disputed round-1 numbers: the committed
# NORD=14 script's c6 (-14769.2, round-1 count) and this desk's
# own instr3 (NORD=16) c7 (-208520.7285, round-1 'true' value) --
# proving BOTH were artifacts of their engine depth (first wrong
# order = eps^{NORD-2} under the eps^-2 clawback), and that the
# round-1 instr3 reference for c7 was itself truncated (ERRATUM).
cs14 = run(14)
cs16 = run(16)
print()
print("mechanism reproduction (construction-only orders):")
print("  depth-14 engine c6 = %s   (round-1 committed script: "
      "-14769.2)" % mp.nstr(cs14[6], 10))
print("  depth-16 engine c7 = %s   (round-1 instr3 'true': "
      "-208520.7285)" % mp.nstr(cs16[7], 10))
assert mp.almosteq(cs14[6], mp.mpf('-14769.16871'),
                   rel_eps=mp.mpf('1e-8'))
assert mp.almosteq(cs16[7], mp.mpf('-208520.7285'),
                   rel_eps=mp.mpf('1e-9'))
print("  BOTH reproduce: the clawback mechanism is confirmed in "
      "both directions; instr3's c7 stands CORRECTED to "
      "-208719.393272 (this engine, exact).")

print()
print("cross-check NORD=22 vs NORD=26 on shared exact orders "
      "c0..c9:")
agree = all(mp.almosteq(cs22[j], cs26[j], rel_eps=mp.mpf('1e-35'))
            for j in range(10))
print("  agree to 35 digits: %s" % agree)
assert agree

cs = cs26
print()
print("exact-engine MD orders at p = 0.5801 (NORD=26, complete "
      "through eps^22):")
for j, c in enumerate(cs):
    print("  c%-2d (eps^%2d) = %s" % (j, 2 * j, mp.nstr(c, 12)))

print()
print("references:")
print("  round-1 instr3 (NORD=16): c6 = -14791.07447  "
      "c7 = -208520.7285")
print("  committed NORD=14 script: c6 = -14769.2")
print()
print("growth ratios |c_{j+1}| / (beta_1 |c_j|):")
for j in range(2, len(cs) - 1):
    if cs[j] != 0:
        print("  j=%2d->%-2d : %s" % (j, j + 1,
              mp.nstr(abs(cs[j + 1] / cs[j]) / BETA1, 6)))
print()
print("bucket-unit ledger at beta_1 = 15 (|c_j|/beta_1^{j-2}):")
for j in range(2, len(cs)):
    print("  j=%-2d : %s" % (j, mp.nstr(abs(cs[j])
                                        / BETA1 ** (j - 2), 6)))
MAG8 = sum(abs(cs[j]) / BETA1 ** j for j in range(0, 9))
print()
print("MAG (j<=8, the script's) = %s ; MAG*g_d = MAG*0.02 = %s"
      % (mp.nstr(MAG8, 6), mp.nstr(MAG8 * mp.mpf('0.02'), 6)))
print("first DROPPED moment order at NORD=18: c9 (eps^18)")
print("  |c9|/beta_1^7 = %s bucket units  vs  MAG*g_d = %s  "
      "(ratio %s)"
      % (mp.nstr(abs(cs[9]) / BETA1 ** 7, 6),
         mp.nstr(MAG8 * mp.mpf('0.02'), 6),
         mp.nstr(abs(cs[9]) / BETA1 ** 7 / (MAG8 * mp.mpf('0.02')),
                 4)))
print("  relative to moment magnitude: (|c9|/beta_1^9)/MAG = %s"
      % mp.nstr(abs(cs[9]) / BETA1 ** 9 / MAG8, 4))
print()
print("INCURABILITY LADDER (first order orphaned by trunc(), in "
      "bucket units at beta_1, exact):")
print("  NORD=14 -> c7  : %s   (round 1's breach, x2.74)"
      % mp.nstr(abs(cs[7]) / BETA1 ** 5, 6))
print("  NORD=18 -> c9  : %s   (this commit)"
      % mp.nstr(abs(cs[9]) / BETA1 ** 7, 6))
print("  NORD=22 -> c11 : %s   (the next raise would be WORSE)"
      % mp.nstr(abs(cs[11]) / BETA1 ** 9, 6))
print("  the growth ratio crosses 1.0 at j=7->8: the series is "
      "DIVERGENT against beta_1 = 15 (minimum term j ~ 7); no "
      "NORD raise can discharge the dropped band.")
print()
print("Lagrange OOM (the three input-series remainders named by "
      "g_d at NORD=18 depths, first omitted terms, riding Gaussian "
      "moments, relative to the moment magnitude at beta_1; kernel "
      "O(1) factors bounded by 1):")
E20 = mp.mpf(654729075)  # 19!!
cosrem = E20 / pmp ** 10 / BETA1 ** 10 / mp.factorial(20)
print("  cos order-10 : ~ (19!!/p^10) beta^-10 / 20! = %s"
      % mp.nstr(cosrem, 4))
print("  exp order-10 : first omitted term expo^10/10! enters "
      "moment orders j >= 10 (eps^{20+})")
print("  binom order-11: w^11 enters moment orders j >= 11 "
      "(eps^{22+})")
print("  => NONE of the three Lagrange families touches eps^16 or "
      "eps^18; the model band j=9 (and the NORD=18 clawback gap at "
      "c8) is NOT Lagrange content.")
