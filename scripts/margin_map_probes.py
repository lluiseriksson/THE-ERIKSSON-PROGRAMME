"""DESIGN-ONLY probe completion (the fine map crashed at probe14 on
the int(NaN) bite, ghost #25; module repaired with the plain-branch
fallback). Reruns the three missing probes. All values DESIGN
ENCLOSURES; hashes in transcript."""
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
    # INCIDENT #26 CURE: print the five totals and Wc ALWAYS, and
    # guard the q division - an arb division by a zero-containing
    # <D> ball yields [nan, nan] and silently destroys the line
    # (probe14, autopsied 2026-07-10: all cells finite, all totals
    # finite, <D> sign unresolved at dz=0.30; the nan was born HERE).
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
              "UNRESOLVED at this dz - q undefined (%d cells); "
              "refine dz(beta)" % (tag, t1, t2, b1, b2, c1+c2),
              flush=True)


if __name__ == "__main__":
    src = open(__file__, "rb").read()
    msrc = open(m.__file__, "rb").read()
    print("=== DESIGN-ONLY PROBE COMPLETION (dz=%.2f) ===" % DZ,
          flush=True)
    print("script sha256 : %s" % hashlib.sha256(src).hexdigest(),
          flush=True)
    print("module sha256 : %s (post ghost-#25 repair)"
          % hashlib.sha256(msrc).hexdigest(), flush=True)
    t0 = time.time()
    w = Fraction(1, 100)
    for (tq, bq, tag) in [(Fraction(3, 2), Fraction(14), "[probe14]"),
                          (Fraction(5, 2), Fraction(15), "[probe25]"),
                          (Fraction(29, 10), Fraction(15), "[probeBD]")]:
        design_q(tq, tq + w, bq, bq + Fraction(5, 100), tag)
    print("probes complete (%.0fs) - design only." % (time.time()-t0),
          flush=True)
