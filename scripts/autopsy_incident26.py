"""INCIDENT #26 AUTOPSY (design-only): probe14 (t[1.5,1.51],
b[14,14.05], dz=0.30) returned q = [nan, nan] THROUGH the repaired
module (post ghost-#25, sha256 834802f9...). Two hypotheses the
existing output cannot discriminate (margin_map_probes.py prints only
q, never the five totals):

  HYPOTHESIS A (cell-level leak): some exp-branch cell produces a
  non-finite contribution that the #25 fallback misses - the fallback
  checks only the MIDPOINTS of Gx, Gy for NaN; a ball with finite
  midpoint but non-finite radius (R lower end tiny-positive =>
  enormous but finite gradient => degenerate L_lin / r.exp()) walks
  past it.

  HYPOTHESIS B (presentation defect, no cell leak): every cell is
  finite, but the fallback's direct e^z enclosures over min-size
  cells at beta=14 are wide enough that the <D> total's ball contains
  0; the NaN is then born in the LAST LINE of the probe script,
  q = Wc/KD**2 - division by a ball containing zero.

This script reruns the same box with (1) a per-cell finiteness check
that CRASHES LOUDLY with exact cell coords + branch diagnostics at
the first offender (crash-not-spin, the #22-family doctrine), (2) a
fallback-trigger counter, (3) the five totals printed as balls, and
(4) the q division GUARDED: if KD's ball contains 0, say so instead
of printing NaN. DESIGN ONLY - no certificate touches this path.
"""
from fractions import Fraction
import hashlib
import math
import time

import exp_integrator_arb as m
from exp_integrator_arb import (V2, arb, ball_lo, ball_hi, D, hull,
                                safe_sqrt)

DZ = 0.3
T1, T2 = Fraction(3, 2), Fraction(151, 100)
B1, B2 = Fraction(14), Fraction(281, 20)

fallback_hits = [0]
_orig_cell = V2.cell


def counting_cell(self, x1, x2, y1, y2, Eb):
    """wrap V2.cell only to count #25-fallback triggers (same test the
    module applies: NaN midpoint of Gx or Gy inside the exp branch)."""
    X = hull(arb(x1)/D, arb(x2)/D)
    Y = hull(arb(y1)/D, arb(y2)/D)
    S, A, P, Q, R2, z = self.geom(X, Y)
    if float(ball_hi(z)) >= 4:
        R = safe_sqrt(R2)
        dR2x = 4*(Q - self.c0**2)*(self.PI/2)*(self.PI*X).sin()
        dR2y = 4*(P - self.c0**2)*(self.PI/2)*(self.PI*Y).sin()
        Gx = self.B*dR2x/R
        Gy = self.B*dR2y/R
        gxm = (float(ball_lo(Gx))+float(ball_hi(Gx)))/2
        gym = (float(ball_lo(Gy))+float(ball_hi(Gy)))/2
        if math.isnan(gxm) or math.isnan(gym):
            fallback_hits[0] += 1
    return _orig_cell(self, x1, x2, y1, y2, Eb)


V2.cell = counting_cell


def integrate_instrumented(pt, Eb, dzmax, hmin=30, max_cells=3000000):
    """copy of m.integrate with the per-cell finiteness check; any
    non-finite contribution dumps the cell and raises."""
    stack = [(0, D, 0, D)]
    tot = [arb(0)]*5
    cells = 0
    while stack:
        x1, x2, y1, y2 = stack.pop()
        X = hull(arb(x1)/D, arb(x2)/D)
        Y = hull(arb(y1)/D, arb(y2)/D)
        _, _, _, _, _, z = pt.geom(X, Y)
        dz = float(ball_hi(z)) - float(ball_lo(z))
        if dz > dzmax and (x2-x1) > hmin and cells + len(stack) < max_cells:
            xm = (x1+x2)//2; ym = (y1+y2)//2
            stack += [(x1, xm, y1, ym), (xm, x2, y1, ym),
                      (x1, xm, ym, y2), (xm, x2, ym, y2)]
            continue
        vals = pt.cell(x1, x2, y1, y2, Eb)
        for i in range(5):
            if not vals[i].is_finite():
                names = ["KNc", "KD", "KNt", "GNc", "GD"]
                print("NON-FINITE CELL CONTRIBUTION (HYPOTHESIS A "
                      "CONFIRMED)", flush=True)
                print("  component %s = %s" % (names[i], vals[i].str(10)),
                      flush=True)
                print("  cell x[%d,%d] y[%d,%d] (units of 1e-6 of "
                      "[0,1]^2)" % (x1, x2, y1, y2), flush=True)
                print("  z = [%s, %s] dz = %.6f  size = %d x %d"
                      % (ball_lo(z).str(10), ball_hi(z).str(10), dz,
                         x2-x1, y2-y1), flush=True)
                print("  fallback hits so far: %d" % fallback_hits[0],
                      flush=True)
                raise RuntimeError("incident #26: first offending cell "
                                   "dumped above")
            tot[i] += vals[i]
        cells += 1
    return tot, cells


def main():
    src = open(__file__, "rb").read()
    msrc = open(m.__file__, "rb").read()
    print("=== INCIDENT #26 AUTOPSY (probe14 box, dz=%.2f) ===" % DZ,
          flush=True)
    print("script sha256 : %s" % hashlib.sha256(src).hexdigest(),
          flush=True)
    print("module sha256 : %s" % hashlib.sha256(msrc).hexdigest(),
          flush=True)
    t0 = time.time()
    pt = V2((T1.numerator, T1.denominator),
            (B1.numerator, B1.denominator), prec=90,
            t_q2=(T2.numerator, T2.denominator),
            b_q2=(B2.numerator, B2.denominator))
    tot, c1 = integrate_instrumented(pt, arb(0), dzmax=0.8)
    E = tot[0]/tot[1]
    print("pass1: %d cells, fallback hits %d, E = [%s, %s]"
          % (c1, fallback_hits[0], ball_lo(E).str(8), ball_hi(E).str(8)),
          flush=True)
    eb = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    fallback_hits[0] = 0
    tot, c2 = integrate_instrumented(pt, arb(eb)/D, dzmax=DZ)
    KNc, KD, KNt, GNc, GD = tot
    names = ["KNc", "KD", "KNt", "GNc", "GD"]
    print("pass2: %d cells, fallback hits %d" % (c2, fallback_hits[0]),
          flush=True)
    for n, v in zip(names, tot):
        print("  %s = [%s, %s]  finite: %s" %
              (n, ball_lo(v).str(8), ball_hi(v).str(8), v.is_finite()),
              flush=True)
    Wc = KNt*KD + GNc*KD - KNc*GD
    print("  Wc = [%s, %s]  finite: %s" %
          (ball_lo(Wc).str(8), ball_hi(Wc).str(8), Wc.is_finite()),
          flush=True)
    kd_contains_zero = not (bool(KD > 0) or bool(KD < 0))
    print("  <D> ball contains 0: %s" % kd_contains_zero, flush=True)
    if kd_contains_zero:
        print("HYPOTHESIS B CONFIRMED: all cells finite, all totals "
              "finite, but <D> straddles 0 - q = Wc/<D>^2 is an arb "
              "division by a zero-containing ball => [nan, nan]. The "
              "'leak' is a PRESENTATION defect in the probe script's "
              "last line, not a fallback defect.", flush=True)
    else:
        q = Wc/KD**2
        print("  q = [%s, %s]  finite: %s" %
              (ball_lo(q).str(8), ball_hi(q).str(8), q.is_finite()),
              flush=True)
        if not q.is_finite():
            print("UNEXPECTED: totals finite, KD sign resolved, q "
                  "non-finite - NEW mechanism, dump above is the "
                  "evidence.", flush=True)
    print("autopsy complete (%.0fs)" % (time.time()-t0), flush=True)


if __name__ == "__main__":
    main()
