"""WIDTH PROFILER (design-only): box 14 (t[1.5,1.51], b[14,14.05])
resists dz refinement (v55: enclosure unchanged from dz=0.30/3M to
dz=0.15/12M). This run names the culprit: for each cell, record the
WIDTH of its KD contribution (the sign-blocking component), keep the
top 20, and histogram width by (branch, z-range, cell size).
Hypotheses on trial:
  H-hmin: min-size cells (hmin floor) near the R=0 manifold - the
          subdivision floor, not dz, binds.
  H-single: a few dominator cells elsewhere (fallback or plain).
  H-diffuse: width is spread over millions of cells (then only a
          finer D-mesh or higher precision helps).
dz=0.30 (the cheap setting - v55 showed dz does not matter here).
"""
from fractions import Fraction
import hashlib
import heapq
import time

import exp_integrator_arb as m
from exp_integrator_arb import V2, arb, ball_lo, ball_hi, D, hull

DZ = 0.3
T1, T2 = Fraction(3, 2), Fraction(151, 100)
B1, B2 = Fraction(14), Fraction(281, 20)


def profile():
    pt = V2((T1.numerator, T1.denominator),
            (B1.numerator, B1.denominator), prec=90,
            t_q2=(T2.numerator, T2.denominator),
            b_q2=(B2.numerator, B2.denominator))
    # pass 1 for Ebar (cheap)
    tot, c1 = m.integrate(pt, arb(0), dzmax=0.8)
    E = tot[0]/tot[1]
    eb = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    Eb = arb(eb)/D
    print("pass1 done (%d cells), Ebar = %d/1e6" % (c1, eb), flush=True)

    stack = [(0, D, 0, D)]
    tot = [arb(0)]*5
    cells = 0
    top = []            # (width, cellinfo) min-heap, keep top 20
    hist = {}           # (branch, zbin, sizebin) -> [count, widthsum]
    t0 = time.time()
    while stack:
        x1, x2, y1, y2 = stack.pop()
        X = hull(arb(x1)/D, arb(x2)/D)
        Y = hull(arb(y1)/D, arb(y2)/D)
        _, _, _, _, _, z = pt.geom(X, Y)
        dz = float(ball_hi(z)) - float(ball_lo(z))
        if dz > DZ and (x2-x1) > 30 and cells + len(stack) < 3000000:
            xm = (x1+x2)//2; ym = (y1+y2)//2
            stack += [(x1, xm, y1, ym), (xm, x2, y1, ym),
                      (x1, xm, ym, y2), (xm, x2, ym, y2)]
            continue
        vals = pt.cell(x1, x2, y1, y2, Eb)
        kd = vals[1]
        wdt = 2*float(kd.rad())
        zhi = float(ball_hi(z))
        branch = "plain" if zhi < 4 else "exp"
        if (x2-x1) <= 60:
            branch += "-min"        # at/near the hmin floor
        zbin = int(zhi // 10)*10
        szbin = (x2-x1)
        key = (branch, zbin)
        e = hist.setdefault(key, [0, 0.0])
        e[0] += 1
        e[1] += wdt
        if len(top) < 20:
            heapq.heappush(top, (wdt, x1, x2, y1, y2, zhi, dz, branch))
        elif wdt > top[0][0]:
            heapq.heapreplace(top, (wdt, x1, x2, y1, y2, zhi, dz, branch))
        for i in range(5):
            tot[i] += vals[i]
        cells += 1
        if cells % 500000 == 0:
            print("  ... %d cells (%.0fs)" % (cells, time.time()-t0),
                  flush=True)
    KD = tot[1]
    print("pass2 done: %d cells; KD = [%s, %s], total width %.4e"
          % (cells, ball_lo(KD).str(6), ball_hi(KD).str(6),
             2*float(KD.rad())), flush=True)
    print("--- width histogram by (branch, z-decade) ---", flush=True)
    for key in sorted(hist, key=lambda k: -hist[k][1]):
        cnt, ws = hist[key]
        print("  %-10s z~%3d : %8d cells, width sum %.4e"
              % (key[0], key[1], cnt, ws), flush=True)
    print("--- top 20 width-contributing cells (KD) ---", flush=True)
    for e in sorted(top, reverse=True):
        wdt, x1, x2, y1, y2, zhi, dz, branch = e
        print("  width %.4e  x[%d,%d] y[%d,%d] size %d  z_hi %.2f "
              "dz %.3f  %s" % (wdt, x1, x2, y1, y2, x2-x1, zhi, dz,
                               branch), flush=True)


if __name__ == "__main__":
    src = open(__file__, "rb").read()
    msrc = open(m.__file__, "rb").read()
    print("=== WIDTH PROFILER box14 (dz=%.2f) ===" % DZ, flush=True)
    print("script sha256 : %s" % hashlib.sha256(src).hexdigest(),
          flush=True)
    print("module sha256 : %s" % hashlib.sha256(msrc).hexdigest(),
          flush=True)
    profile()
    print("PROFILE COMPLETE", flush=True)
