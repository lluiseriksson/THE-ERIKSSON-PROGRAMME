"""DESIGN-ONLY dz(beta) PILOT (task queue item 3, acta v58/v60).

The dz(beta) scaling lesson has four specimens (probe25, probeBD,
probe14 v1, probe14f) and no formula: at dz=0.30 the q-enclosure
width is ~0.03 at beta=8 but 1.5-1.9 at beta=14-15 (v2 priority
subdivision, cap no longer the culprit after v56/v59).  This pilot
MEASURES width(dz, beta) at the two standing high-beta probe boxes
so the [3,15] campaign can size dz(beta) from data, not guesswork:

  box A = t[3/2, 3/2+1/100]   x b[14, 14+1/20]  (probe14 territory)
  box B = t[29/10, 29/10+1/100] x b[15, 15+1/20] (probeBD territory)

stages: (A, dz=0.15, cap 8M), (B, dz=0.15, cap 8M),
        (A, dz=0.10, cap 16M), (B, dz=0.10, cap 16M).

Known dz=0.30 anchors for the fit (committed transcripts):
  A: width 1.514 (probes_v2_transcript_1c61089f);
  B: width 1.763 (margin_map_probes_out_dc3ab825, v1 - drained, so
     comparable).

Machinery: integrate_priority IMPORTED from margin_map_probes_v2
(byte-identical subdivision, module exp_integrator_arb 834802f9
encloses every cell).  Each stage prints its enclosure immediately
(flush) so a killed run keeps its completed stages.  Design-only:
no certificate claims; numbers exist when this transcript is
committed (regime pt 7, extended by incident #27).
"""
from fractions import Fraction
import hashlib
import time

import exp_integrator_arb as m
from exp_integrator_arb import V2, arb, ball_lo, ball_hi, D
import margin_map_probes_v2 as p2
from margin_map_probes_v2 import integrate_priority


def design_q_dz(t1, t2, b1, b2, dz, cap, tag):
    pt = V2((t1.numerator, t1.denominator),
            (b1.numerator, b1.denominator), prec=90,
            t_q2=(t2.numerator, t2.denominator),
            b_q2=(b2.numerator, b2.denominator))
    t0 = time.time()
    tot, c1 = integrate_priority(pt, arb(0), dzmax=0.8)
    E = tot[0]/tot[1]
    eb = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    tot, c2 = integrate_priority(pt, arb(eb)/D, dzmax=dz,
                                 max_cells=cap)
    KNc, KD, KNt, GNc, GD = tot
    Wc = KNt*KD + GNc*KD - KNc*GD
    for nm, v in zip(("KNc", "KD", "KNt", "GNc", "GD", "Wc"),
                     (KNc, KD, KNt, GNc, GD, Wc)):
        print("  %s %s = [%s, %s]" % (tag, nm, ball_lo(v).str(6),
                                      ball_hi(v).str(6)), flush=True)
    if bool(KD > 0) or bool(KD < 0):
        q = Wc/KD**2
        print("PILOT ENCLOSURE %s t[%s,%s] b[%s,%s] dz=%.2f cap %d: "
              "q = [%s, %s] width %.4f (%d cells, %.0fs)"
              % (tag, t1, t2, b1, b2, dz, cap,
                 ball_lo(q).str(6), ball_hi(q).str(6),
                 float(ball_hi(q))-float(ball_lo(q)), c1+c2,
                 time.time()-t0), flush=True)
    else:
        print("PILOT %s t[%s,%s] b[%s,%s] dz=%.2f cap %d: <D> sign "
              "UNRESOLVED (%d cells, %.0fs)"
              % (tag, t1, t2, b1, b2, dz, cap, c1+c2,
                 time.time()-t0), flush=True)


if __name__ == "__main__":
    src = open(__file__, "rb").read()
    msrc = open(m.__file__, "rb").read()
    psrc = open(p2.__file__, "rb").read()
    print("=== dz(beta) PILOT, priority subdivision ===", flush=True)
    print("script sha256 : %s" % hashlib.sha256(src).hexdigest(),
          flush=True)
    print("module sha256 : %s" % hashlib.sha256(msrc).hexdigest(),
          flush=True)
    print("probes_v2 sha256 : %s" % hashlib.sha256(psrc).hexdigest(),
          flush=True)
    t0 = time.time()
    w = Fraction(1, 100)
    bw = Fraction(1, 20)
    A = (Fraction(3, 2), Fraction(3, 2) + w,
         Fraction(14), Fraction(14) + bw)
    B = (Fraction(29, 10), Fraction(29, 10) + w,
         Fraction(15), Fraction(15) + bw)
    design_q_dz(*A, 0.15, 8000000, "[pilotA-dz15]")
    design_q_dz(*B, 0.15, 8000000, "[pilotB-dz15]")
    design_q_dz(*A, 0.10, 16000000, "[pilotA-dz10]")
    design_q_dz(*B, 0.10, 16000000, "[pilotB-dz10]")
    print("pilot complete (%.0fs) - design only." % (time.time()-t0),
          flush=True)
