"""DESIGN-ONLY probe machinery v2: PRIORITY SUBDIVISION (the v56
cure). The v1 LIFO stack strands unprocessed quadrants as giant
cells when the cell cap binds (box 14: one half-domain cell carried
99.99% of the width while 2.65M cells refined territory 18 orders
below the saddle). v2 processes a max-heap keyed by the cell's
log-width proxy  z_hi + ln(area): the worst offender is always
subdivided first, so when the budget runs out the UNREFINED
remainder is the most innocuous, not the saddle quadrant. Same
rigor (every cell still enclosed by the audited module 834802f9);
same dz criterion; same caps. First client: box 14 at dz=0.30 /
cap 3M, where v1 failed to resolve <D>'s sign at 12M.
"""
from fractions import Fraction
import hashlib
import heapq
import math
import time

import exp_integrator_arb as m
from exp_integrator_arb import V2, arb, ball_lo, ball_hi, D, hull

DZ = 0.3
MAXC = 3000000


def integrate_priority(pt, Eb, dzmax=DZ, hmin=30, max_cells=MAXC):
    def keyof(x1, x2, y1, y2):
        X = hull(arb(x1)/D, arb(x2)/D)
        Y = hull(arb(y1)/D, arb(y2)/D)
        _, _, _, _, _, z = pt.geom(X, Y)
        zhi = float(ball_hi(z))
        dz = zhi - float(ball_lo(z))
        area = float(x2-x1)*float(y2-y1)
        return -(zhi + math.log(area)), dz

    k0, dz0 = keyof(0, D, 0, D)
    heap = [(k0, dz0, 0, D, 0, D)]
    tot = [arb(0)]*5
    cells = 0
    budget_hit = False
    t0 = time.time()
    while heap:
        key, dz, x1, x2, y1, y2 = heapq.heappop(heap)
        if dz > dzmax and (x2-x1) > hmin and \
                cells + len(heap) < max_cells:
            xm = (x1+x2)//2; ym = (y1+y2)//2
            for q in ((x1, xm, y1, ym), (xm, x2, y1, ym),
                      (x1, xm, ym, y2), (xm, x2, ym, y2)):
                kq, dzq = keyof(*q)
                heapq.heappush(heap, (kq, dzq) + q)
            continue
        if dz > dzmax and (x2-x1) > hmin:
            budget_hit = True
        vals = pt.cell(x1, x2, y1, y2, Eb)
        for i in range(5):
            tot[i] += vals[i]
        cells += 1
        if cells % 500000 == 0:
            print("  ... %d cells (%.0fs)" % (cells, time.time()-t0),
                  flush=True)
    if budget_hit:
        print("  NOTE: cell budget bound before dz criterion was met "
              "everywhere (finalized coarse cells are the lowest-"
              "priority ones by construction).", flush=True)
    return tot, cells


def design_q(t1, t2, b1, b2, tag):
    pt = V2((t1.numerator, t1.denominator),
            (b1.numerator, b1.denominator), prec=90,
            t_q2=(t2.numerator, t2.denominator),
            b_q2=(b2.numerator, b2.denominator))
    tot, c1 = integrate_priority(pt, arb(0), dzmax=0.8)
    E = tot[0]/tot[1]
    eb = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    tot, c2 = integrate_priority(pt, arb(eb)/D, dzmax=DZ)
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
    print("=== DESIGN PROBES v2, priority subdivision (dz=%.2f, "
          "cap %d) ===" % (DZ, MAXC), flush=True)
    print("script sha256 : %s" % hashlib.sha256(src).hexdigest(),
          flush=True)
    print("module sha256 : %s" % hashlib.sha256(msrc).hexdigest(),
          flush=True)
    t0 = time.time()
    w = Fraction(1, 100)
    design_q(Fraction(3, 2), Fraction(3, 2) + w,
             Fraction(14), Fraction(14) + Fraction(5, 100),
             "[probe14v2]")
    print("v2 probe complete (%.0fs) - design only."
          % (time.time()-t0), flush=True)
