"""DESIGN-ONLY probe14 refinement (incident #26 aftermath): the box
t[1.5,1.51] x b[14,14.05] left <D>'s sign unresolved at dz=0.30 with
the 3M cell cap (all enclosures finite - the #25/#26 doctrine:
finiteness is the integrator's contract, sign resolution is the
design's). Rerun at dz=0.15 with a 12M cap, cured printing (five
totals + guarded q division). Feeds the L cross-table (v44)."""
from fractions import Fraction
import hashlib
import time

import exp_integrator_arb as m
from exp_integrator_arb import V2, integrate, arb, ball_lo, ball_hi, D

DZ = 0.15
MAXC = 12000000


def design_q(t1, t2, b1, b2, tag):
    pt = V2((t1.numerator, t1.denominator),
            (b1.numerator, b1.denominator), prec=90,
            t_q2=(t2.numerator, t2.denominator),
            b_q2=(b2.numerator, b2.denominator))
    tot, c1 = integrate(pt, arb(0), dzmax=0.8, max_cells=MAXC)
    E = tot[0]/tot[1]
    eb = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    tot, c2 = integrate(pt, arb(eb)/D, dzmax=DZ, max_cells=MAXC)
    KNc, KD, KNt, GNc, GD = tot
    Wc = KNt*KD + GNc*KD - KNc*GD
    for nm, v in zip(("KNc", "KD", "KNt", "GNc", "GD", "Wc"),
                     (KNc, KD, KNt, GNc, GD, Wc)):
        print("  %s %s = [%s, %s]" % (tag, nm, ball_lo(v).str(6),
                                      ball_hi(v).str(6)), flush=True)
    if bool(KD > 0) or bool(KD < 0):
        q = Wc/KD**2
        print("DESIGN ENCLOSURE %s t[%s,%s] b[%s,%s]: q = [%s, %s] "
              "width %.4f (%d cells)" % (tag, t1, t2, b1, b2,
              ball_lo(q).str(6), ball_hi(q).str(6),
              float(ball_hi(q))-float(ball_lo(q)), c1+c2), flush=True)
    else:
        print("DESIGN ENCLOSURE %s t[%s,%s] b[%s,%s]: <D> sign "
              "UNRESOLVED at dz=%.2f cap %d (%d cells)"
              % (tag, t1, t2, b1, b2, DZ, MAXC, c1+c2), flush=True)


if __name__ == "__main__":
    src = open(__file__, "rb").read()
    msrc = open(m.__file__, "rb").read()
    print("=== DESIGN-ONLY PROBE14 REFINEMENT (dz=%.2f, cap %d) ==="
          % (DZ, MAXC), flush=True)
    print("script sha256 : %s" % hashlib.sha256(src).hexdigest(),
          flush=True)
    print("module sha256 : %s" % hashlib.sha256(msrc).hexdigest(),
          flush=True)
    t0 = time.time()
    w = Fraction(1, 100)
    design_q(Fraction(3, 2), Fraction(3, 2) + w,
             Fraction(14), Fraction(14) + Fraction(5, 100),
             "[probe14f]")
    print("probe14 refinement complete (%.0fs) - design only."
          % (time.time()-t0), flush=True)
