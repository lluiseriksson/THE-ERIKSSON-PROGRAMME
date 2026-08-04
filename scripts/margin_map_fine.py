"""DESIGN-ONLY fine margin map (task #89 ignition; convention of
conv:mass). dz = 0.3: fine enough to RESOLVE the sign of q (the 0.5
map measured cost only). Nine 3x3 sub-boxes + probe boxes at
(t, beta) = (1.5, 12), (1.5, 14), (2.5, 15) and near the moving
boundary (2.9, 15) - the L-constant re-derivation inputs (finite
differences of q) and the variation-bound rule feed on this output.
ALL VALUES ARE DESIGN ENCLOSURES; certificates live in harvest
transcripts only. Prints its own sha256 and the module's."""
from fractions import Fraction
import hashlib
import time

import exp_integrator_arb as m
from exp_integrator_arb import V2, integrate, arb, ball_lo, ball_hi, D

DZ = 0.3


def design_q(t1, t2, b1, b2, tag):
    pt = V2((t1.numerator, t1.denominator),
            (b1.numerator, b1.denominator), prec=90,
            t_q2=(t2.numerator, t2.denominator),
            b_q2=(b2.numerator, b2.denominator))
    tot, c1 = integrate(pt, arb(0), dzmax=0.8)
    E = tot[0]/tot[1]
    eb = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    tot, c2 = integrate(pt, arb(eb)/D, dzmax=DZ)
    KNc, KD, KNt, GNc, GD = tot
    Wc = KNt*KD + GNc*KD - KNc*GD
    q = Wc/KD**2
    print("DESIGN ENCLOSURE %s t[%s,%s] b[%s,%s]: q = [%s, %s] "
          "width %.4f (%d cells)" % (tag, t1, t2, b1, b2,
          ball_lo(q).str(6), ball_hi(q).str(6),
          float(ball_hi(q))-float(ball_lo(q)), c1+c2), flush=True)


if __name__ == "__main__":
    src = open(__file__, "rb").read()
    msrc = open(m.__file__, "rb").read()
    print("=== DESIGN-ONLY FINE MARGIN MAP (dz=%.2f) ===" % DZ,
          flush=True)
    print("map sha256    : %s" % hashlib.sha256(src).hexdigest(),
          flush=True)
    print("module sha256 : %s" % hashlib.sha256(msrc).hexdigest(),
          flush=True)
    t0 = time.time()
    # the harvest 3x3 grid, fine
    T1 = Fraction(15, 10); T2 = Fraction(151, 100)
    B1 = Fraction(8, 1); B2 = Fraction(805, 100)
    for i in range(3):
        ta = T1 + (T2-T1)*i/3; tb = T1 + (T2-T1)*(i+1)/3
        for j in range(3):
            ba = B1 + (B2-B1)*j/3; bb = B1 + (B2-B1)*(j+1)/3
            design_q(ta, tb, ba, bb, "[grid]")
    # probes: high beta (cheap half per the L-constants) + boundary
    w = Fraction(1, 100)
    for (tq, bq, tag) in [(Fraction(3, 2), Fraction(12), "[probe12]"),
                          (Fraction(3, 2), Fraction(14), "[probe14]"),
                          (Fraction(5, 2), Fraction(15), "[probe25]"),
                          (Fraction(29, 10), Fraction(15), "[probeBD]")]:
        design_q(tq, tq + w, bq, bq + Fraction(5, 100), tag)
    print("fine map complete (%.0fs total) - design only." %
          (time.time()-t0), flush=True)
