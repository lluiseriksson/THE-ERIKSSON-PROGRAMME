"""PARAMETRIC-FLOOR CONFIRMATION (design-only; v72 rule check).
The v72 diagnosis: pilot box A (t[1.5,1.51] x b[14,14.05]) has
parametric floor ~0.237 > dz = 0.15, unreachable by construction.
Confirmation experiment: the SHRUNK box t[1.5,1.505] x b[14,14.02]
has floor ~ 2(1.861)(0.02) + 2(14)(0.183)(0.005) = 0.100 < 0.15,
so the dz = 0.15 criterion must now be SATISFIABLE: the run should
drain (no cap-bound note) well under the 3M cap, and <D> should
resolve as v59 did at dz = 0.30.  Machinery byte-identical:
integrate_priority imported from margin_map_probes_v2 (module
834802f9).  Transcript exists when committed.
"""
from fractions import Fraction
import hashlib
import time

import exp_integrator_arb as m
from exp_integrator_arb import V2, arb, ball_lo, ball_hi, D
import margin_map_probes_v2 as p2
from margin_map_probes_v2 import integrate_priority

if __name__ == "__main__":
    print("=== parametric-floor confirmation (shrunk box A) ===",
          flush=True)
    for f, tag in ((__file__, "script"), (m.__file__, "module"),
                   (p2.__file__, "probes_v2")):
        print("%s sha256 : %s" % (tag,
              hashlib.sha256(open(f, "rb").read()).hexdigest()),
              flush=True)
    t0 = time.time()
    t1 = Fraction(3, 2); t2 = t1 + Fraction(1, 200)
    b1 = Fraction(14); b2 = b1 + Fraction(1, 50)
    pt = V2((t1.numerator, t1.denominator),
            (b1.numerator, b1.denominator), prec=90,
            t_q2=(t2.numerator, t2.denominator),
            b_q2=(b2.numerator, b2.denominator))
    tot, c1 = integrate_priority(pt, arb(0), dzmax=0.8)
    E = tot[0]/tot[1]
    eb = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    tot, c2 = integrate_priority(pt, arb(eb)/D, dzmax=0.15,
                                 max_cells=3000000)
    KNc, KD, KNt, GNc, GD = tot
    Wc = KNt*KD + GNc*KD - KNc*GD
    for nm, v in zip(("KNc", "KD", "KNt", "GNc", "GD", "Wc"),
                     (KNc, KD, KNt, GNc, GD, Wc)):
        print("  %s = [%s, %s]" % (nm, ball_lo(v).str(6),
                                   ball_hi(v).str(6)), flush=True)
    resolved = bool(KD > 0) or bool(KD < 0)
    if resolved:
        q = Wc/KD**2
        print("CONFIRM shrunk-box t[3/2,301/200] b[14,701/50] "
              "dz=0.15: <D> RESOLVED, q = [%s, %s] width %.4f "
              "(%d cells, %.0fs)" % (ball_lo(q).str(6),
              ball_hi(q).str(6),
              float(ball_hi(q))-float(ball_lo(q)), c1+c2,
              time.time()-t0), flush=True)
    else:
        print("CONFIRM FAILED: <D> sign UNRESOLVED in the shrunk "
              "box (%d cells, %.0fs) - the floor diagnosis needs "
              "revisiting" % (c1+c2, time.time()-t0), flush=True)
