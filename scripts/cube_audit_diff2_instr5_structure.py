"""DIFF ROUND 2, INSTRUMENT 5: structural verification of the
NORD=18 no-orphan claim (item A of the round-2 commission) against
the COMMITTED cascade3c_buckets.py (imported: the committed bytes
run in full, all asserts live).

Claims checked, per moment (7 total):
  S1  the stored coefficient list has length J+1 with
      J = (NORD-1-k0)//2  (coeffs() reaches the last slot);
  S2  the truncated integrand polynomial has only EVEN eps-degrees,
      all < NORD (so eps^16 is the maximal possible even order);
  S3  the plane moment of the truncated integrand (independent
      gmoment re-implementation here) has NO content below k0, NO
      odd content, and its LAST nonzero order is <= k0 + 2J — so
      the finite sum sum_{j<=J} c_j beta^-j IS exactly the
      polynomial's plane moment: no polynomial order is orphaned;
  S4  CONV*fac*coeff(eps, k0+2j) reproduces the stored c_j for
      every j (spot: all seven moments, all orders, symbolic);
  S5  numeric MD c6, c7, c8 at the zone floor pv = 0.5801, for
      adjudication against the NORD=22 exact-Fraction truth
      (instr4); plus MAG, MAG*g_d and ctail at the MD floor.
Design instrument; transcript exists when committed.
"""
import hashlib
import sys

import mpmath as mp
import sympy as sp

print("=== DIFF ROUND 2 / INSTR 5: structure of the NORD=18 "
      "extraction ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
print("importing committed cascade3c_buckets (full run)...",
      flush=True)
import cascade3c_buckets as C3  # noqa: E402  (committed bytes)

sig, tau, p, eps = C3.sig, C3.tau, C3.p, C3.eps
NORD = C3.NORD
CONV = C3.CONV
print("import done; NORD = %d" % NORD, flush=True)
assert NORD == 18


def gmoment_indep(poly):
    """independent plane-moment re-implementation (audit copy)."""
    poly = sp.expand(poly)
    total = 0
    for t_ in poly.as_ordered_terms():
        pd = t_.as_powers_dict()
        ks = int(pd.get(sig, 0))
        ka = int(pd.get(tau, 0))
        if ks % 2 or ka % 2:
            continue
        coeff = t_ / (sig ** ks * tau ** ka)

        def m1(k):
            return sp.sqrt(2 * sp.pi / p) * sp.factorial2(k - 1) \
                / p ** (k // 2) if k > 0 else sp.sqrt(2 * sp.pi / p)
        total += coeff * m1(ks) * m1(ka)
    return sp.expand(total)


ALL = [('mir', nm) + C3.MOM_MIR[nm] for nm in C3.MOM_MIR] + \
      [('main', nm) + C3.MOM_MAIN[nm] for nm in C3.MOM_MAIN]

ok_all = True
for kind, nm, cj, ip_, k0, fac in ALL:
    J = (NORD - 1 - k0) // 2
    s1 = (len(cj) == J + 1)
    degs = sorted({int(t.as_powers_dict().get(eps, 0))
                   for t in sp.expand(ip_).as_ordered_terms()})
    s2 = all(d % 2 == 0 and d < NORD for d in degs)
    M = gmoment_indep(ip_)
    mdegs = sorted({int(t.as_powers_dict().get(eps, 0))
                    for t in M.as_ordered_terms()})
    s3 = all(d % 2 == 0 for d in mdegs) and min(mdegs) >= k0 \
        and max(mdegs) <= k0 + 2 * J
    s4 = all(sp.simplify(CONV * fac * M.coeff(eps, k0 + 2 * j)
                         - cj[j]) == 0 for j in range(J + 1))
    ok = s1 and s2 and s3 and s4
    ok_all = ok_all and ok
    print("  %-4s %-5s k0=%d J=%d len(cj)=%d  int-degs %s..%s  "
          "mom-degs %s..%s  S1 %s S2 %s S3 %s S4 %s -> %s"
          % (kind, nm, k0, J, len(cj), degs[0], degs[-1],
             mdegs[0], mdegs[-1], s1, s2, s3, s4,
             "OK" if ok else "FAIL"), flush=True)

print("STRUCTURE (S1-S4, all seven moments): %s"
      % ("PASS" if ok_all else "FAIL"), flush=True)
assert ok_all

# S5: numeric MD orders at the mirror zone floor
mp.mp.dps = 30
pv = mp.mpf('0.5801')
cj_md = C3.MOM_MIR['MD'][0]
print()
print("S5: committed NORD=18 MD orders at pv = 0.5801:")
vals = []
for j, c in enumerate(cj_md):
    v = C3.numv(c, pv)
    vals.append(v)
    print("  c%d = %s" % (j, mp.nstr(v, 12)))
BETA1 = C3.BETA1
MAG = sum(abs(v) / BETA1 ** j for j, v in enumerate(vals))
ctail = sum(abs(vals[j]) / BETA1 ** (j - 2)
            for j in range(4, len(vals)))
print("  MAG = %s   MAG*g_d = %s   ctail(j=4..%d) = %s"
      % (mp.nstr(MAG, 6), mp.nstr(MAG * mp.mpf('0.02'), 6),
         len(vals) - 1, mp.nstr(ctail, 6)))
print("done.", flush=True)
