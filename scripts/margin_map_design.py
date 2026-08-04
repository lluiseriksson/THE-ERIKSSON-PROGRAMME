"""DESIGN-ONLY margin map for the 3x3 box (audit round 2026-07-10y).

EVERY value printed here is a DESIGN ENCLOSURE at coarse dz: NOT
certificate-grade, NEVER to be mixed with harvest transcripts. The
certificates are the booleans of the harvest transcript (anchored run
1d888e99). This map exists to recover the normalized-margin column
q = Wc/<D>^2 for the in-flight 3x3 (whose script predates the q
print) and to calibrate the adaptive coverage of [6,15]:
box size and dz2 are sized from q, refinement near pi - 1.5/beta.

Provenance: prints its own sha256 and the module's, per the
design-only separation law (values labeled, hashes registered).
"""
from fractions import Fraction
import hashlib
import sys
import time

import exp_integrator_arb as m
from exp_integrator_arb import V2, integrate, arb, ball_lo, ball_hi, D

DZ_DESIGN = 0.5   # coarse: design-grade, sign-agnostic by contract


def design_q(t1, t2, b1, b2):
    pt = V2((t1.numerator, t1.denominator),
            (b1.numerator, b1.denominator), prec=90,
            t_q2=(t2.numerator, t2.denominator),
            b_q2=(b2.numerator, b2.denominator))
    tot, c1 = integrate(pt, arb(0), dzmax=0.8)
    E = tot[0]/tot[1]
    eb = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    tot, c2 = integrate(pt, arb(eb)/D, dzmax=DZ_DESIGN)
    KNc, KD, KNt, GNc, GD = tot
    Wc = KNt*KD + GNc*KD - KNc*GD
    q = Wc/KD**2
    return q, c1 + c2


if __name__ == "__main__":
    src = open(__file__, "rb").read()
    msrc = open(m.__file__, "rb").read()
    print("=== DESIGN-ONLY MARGIN MAP (3x3 box) ===", flush=True)
    print("ALL VALUES BELOW ARE DESIGN ENCLOSURES (coarse dz=%.2f);"
          " certificates live in the harvest transcript ONLY."
          % DZ_DESIGN, flush=True)
    print("map script sha256   : %s"
          % hashlib.sha256(src).hexdigest(), flush=True)
    print("module (%s) sha256  : %s"
          % (m.__file__, hashlib.sha256(msrc).hexdigest()), flush=True)
    t1 = Fraction(15, 10); t2 = Fraction(151, 100)
    b1 = Fraction(8, 1); b2 = Fraction(805, 100)
    for i in range(3):
        ta = t1 + (t2-t1)*i/3; tb = t1 + (t2-t1)*(i+1)/3
        for j in range(3):
            ba = b1 + (b2-b1)*j/3; bb = b1 + (b2-b1)*(j+1)/3
            ts = time.time()
            q, c = design_q(ta, tb, ba, bb)
            print("DESIGN ENCLOSURE sub-box t[%s,%s] b[%s,%s]: "
                  "q = [%s, %s] width %.4f (%d cells, %.0fs)"
                  % (ta, tb, ba, bb, ball_lo(q).str(6),
                     ball_hi(q).str(6),
                     float(ball_hi(q)) - float(ball_lo(q)), c,
                     time.time()-ts), flush=True)
    print("map complete - design only, feeds coverage sizing, not the"
          " certified proposition.", flush=True)
