"""Arb port of exp_integrator.py (v2b) - the [6,15] machine, fast lane.
Same pinned target, same A/B profiles, same parametric sub-box layer:
see the mpmath.iv twin's docstring. Harvest driver at the bottom runs
point -> stability -> 3x3 box in sequence, one transcript.
"""
from flint import arb, ctx
from math import factorial
from fractions import Fraction

D = 10**6
DZMAX = 0.15


def hull(lo, hi):
    # GHOST #22: python-flint's arb.union returns VALID but symmetric-wide
    # balls (union(0,1) = [+/- 1.01]); downstream that widened R^2 past
    # clip0 into sqrt(negative) = NaN, and NaN never exits series loops.
    # ALWAYS use the tight midpoint form.
    return (lo + hi)/2 + ((hi - lo)/2)*arb("0 +/- 1")


def ball_lo(z):
    return arb(z.mid()) - arb(z.rad())


def ball_hi(z):
    return arb(z.mid()) + arb(z.rad())


def clip0(x):
    """kept for values used WITHOUT sqrt; true-square values may carry a
    -ulp lower end from rounding, which is harmless outside sqrt."""
    return x


def safe_sqrt(x):
    """GHOST #22 (the real fix). CONTRACT (audit round 2026-07-10s):

    * APPLIES ONLY to expressions mathematically known nonnegative
      (true squares: R^2, z^2). For such x the enclosing ball satisfies
      ball_hi(x) >= true max >= 0; a lower end below 0 can only be
      rounding slack (the -ulp of ball reconstruction), never truth.
    * ENDPOINTS ARE OUTWARD by construction: ball_lo/ball_hi are
      arb(mid) -/+ arb(rad) computed in ball arithmetic, so each is a
      ball CONTAINING the true endpoint; .sqrt() of each is a ball
      containing the true sqrt; the hull inherits by monotonicity.
    * RETURNS an enclosure of [sqrt(max(0,x_lo)), sqrt(max(0,x_hi))].
    * FINITENESS is checked immediately: a non-finite result raises
      instead of propagating (NaN comparisons are always False and
      would silently corrupt downstream control flow - the #22 chain).
    * Unit tests: scripts/test_safe_sqrt.py ([-ulp,1], [0,0], tiny
      intervals, truly negative input).

    sqrt of a ball whose rounded lower end dips below 0 is NaN in arb,
    and NaN never exits the series loops - hence all of the above."""
    lo = ball_lo(x)
    hi = ball_hi(x)
    if not (lo >= 0):
        lo = arb(0)
    if not (hi >= 0):
        hi = arb(0)
    out = hull(lo.sqrt(), hi.sqrt())
    if not out.is_finite():
        raise RuntimeError("safe_sqrt: non-finite result for x=%s "
                           "(lo=%s hi=%s)" % (x.str(10), lo.str(10),
                                              hi.str(10)))
    return out


def i1_over_z_at(x):
    s = arb(0)
    term = arb(1)/2
    x2q = (x/2)**2
    j = 0
    while True:
        s += term
        r = x2q/(arb(j+1)*arb(j+2))
        nxt = term*r
        if r < arb(1)/2 and nxt < arb(10)**(-45)*s:
            return s + hull(arb(0), nxt/(1-r))
        term = nxt
        j += 1
        if j > 20000:   # defense in depth: NaN never satisfies the exit
            raise RuntimeError(
                "i1_over_z series did not converge after %d terms: "
                "x=%s s=%s term=%s ratio=%s prec=%d (NaN input?)"
                % (j, x.str(10), s.str(10), term.str(10), r.str(10),
                   ctx.prec))


def H_at(x):
    s = arb(0)
    term = arb(1)/8
    x2 = x*x
    j = 0
    while True:
        s += term
        fac = x2/(arb(4)*arb(j+1)*arb(j+3))
        r = fac
        nxt = term*fac
        if r < arb(1)/2 and nxt < arb(10)**(-45)*s:
            return s + hull(arb(0), nxt/(1-r))
        term = nxt
        j += 1
        if j > 20000:
            raise RuntimeError(
                "H series did not converge after %d terms: "
                "x=%s s=%s term=%s ratio=%s prec=%d (NaN input?)"
                % (j, x.str(10), s.str(10), term.str(10), r.str(10),
                   ctx.prec))


def A_enclose(z):
    zl = ball_lo(z); zh = ball_hi(z)
    a_lo = (-zh).exp()*i1_over_z_at(zh)
    a_hi = (-zl).exp()*i1_over_z_at(zl)
    return hull(a_lo, a_hi)


def B_enclose(z):
    zl = ball_lo(z); zh = ball_hi(z)
    lo = (-zh).exp()*H_at(zl)
    hi = (-zl).exp()*H_at(zh)
    return hull(lo, hi)


def L_lin(g_num, h_num, den):
    g = arb(g_num)/den
    h = arb(h_num)/den
    if abs(g_num) < 10:
        m = (abs(g)*h/2).exp()
        return hull(h/m, h*m)
    a = g*h/2
    return (a.exp() - (-a).exp())/g


class V2:
    def __init__(self, t_q, b_q, prec=90, t_q2=None, b_q2=None):
        ctx.prec = prec
        self.prec = prec
        self.T = arb(t_q[0])/arb(t_q[1])
        if t_q2 is not None:
            self.T = hull(self.T, arb(t_q2[0])/arb(t_q2[1]))
        self.B = arb(b_q[0])/arb(b_q[1])
        if b_q2 is not None:
            self.B = hull(self.B, arb(b_q2[0])/arb(b_q2[1]))
        self.C = (self.T/2).cos()
        self.c0 = (self.T/4).cos()
        self.cp = -(self.T/4).sin()/4
        self.S2 = (self.T/2).sin()
        self.Gpre = 32*self.B**3*self.c0*self.cp
        self.PI = arb.pi()

    def geom(self, X, Y):
        S = self.PI*X; A = self.PI*Y
        P = (S/2).sin()**2
        Q = (A/2).sin()**2
        R2 = clip0(4*(self.c0**2*(1-P-Q) + P*Q))
        z = safe_sqrt(4*self.B**2*R2)
        return S, A, P, Q, R2, z

    def trig(self, S, A, Eb):
        cs = S.cos(); ca = A.cos(); c2s = (2*S).cos(); ss = S.sin()
        N = self.C*c2s + ca*(self.C*cs - ss**2)
        Dd = cs + ca
        Nt = -(self.S2/2)*(c2s + ca*cs)
        Nc = N - Eb*Dd
        return Nc, Dd, Nt

    def cell(self, x1, x2, y1, y2, Eb):
        X = hull(arb(x1)/D, arb(x2)/D)
        Y = hull(arb(y1)/D, arb(y2)/D)
        S, A, P, Q, R2, z = self.geom(X, Y)
        Nc, Dd, Nt = self.trig(S, A, Eb)
        Af = A_enclose(z)
        Bf = B_enclose(z)
        Kslow = 2*self.B*Af
        Gslow = self.Gpre*(1-P-Q)*Bf
        if float(ball_hi(z)) < 4:
            area = (arb(x2-x1)/D)*(arb(y2-y1)/D)*self.PI**2
            core = z.exp()*area
            return (core*Kslow*Nc, core*Kslow*Dd, core*Kslow*Nt,
                    core*Gslow*Nc, core*Gslow*Dd)
        xc2 = x1 + x2; yc2 = y1 + y2
        Xc = arb(xc2)/(2*D); Yc = arb(yc2)/(2*D)
        _, _, _, _, _, zc = self.geom(Xc, Yc)
        R = safe_sqrt(R2)
        dR2x = 4*(Q - self.c0**2)*(self.PI/2)*(self.PI*X).sin()
        dR2y = 4*(P - self.c0**2)*(self.PI/2)*(self.PI*Y).sin()
        Gx = self.B*dR2x/R
        Gy = self.B*dR2y/R
        gx_num = int(round((float(ball_lo(Gx))+float(ball_hi(Gx)))/2*2*D))
        gy_num = int(round((float(ball_lo(Gy))+float(ball_hi(Gy)))/2*2*D))
        gx = arb(gx_num)/(2*D); gy = arb(gy_num)/(2*D)
        hx = x2 - x1; hy = y2 - y1
        r = (Gx-gx)*hull(arb(-hx)/(2*D), arb(hx)/(2*D)) \
            + (Gy-gy)*hull(arb(-hy)/(2*D), arb(hy)/(2*D))
        Lx = L_lin(gx_num, 2*hx, 2*D)
        Ly = L_lin(gy_num, 2*hy, 2*D)
        core = zc.exp()*Lx*Ly*r.exp()*self.PI**2
        return (core*Kslow*Nc, core*Kslow*Dd, core*Kslow*Nt,
                core*Gslow*Nc, core*Gslow*Dd)


def integrate(pt, Eb, dzmax=DZMAX, hmin=30, max_cells=3000000):
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
            tot[i] += vals[i]
        cells += 1
    return tot, cells


def certify_point(t_q, b_q, dz1=0.8, dz2=0.15, prec=90, tag=""):
    pt = V2(t_q, b_q, prec=prec)
    tot, c1 = integrate(pt, arb(0), dzmax=dz1)
    E = tot[0]/tot[1]
    eb_num = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    Eb = arb(eb_num)/D
    # Print the ENCLOSURE of E, not just the rational center: Ebar is a
    # CHOICE (any constant works in the centered target), so the cross-
    # implementation witness is enclosure consistency (E_iv and E_arb
    # intersect and both contain the common truth), never Ebar equality.
    print("%spass1: %d cells, E enclosure = [%.6f, %.6f], Ebar = %d/1e6"
          % (tag, c1, float(ball_lo(E)), float(ball_hi(E)), eb_num),
          flush=True)
    tot, c2 = integrate(pt, Eb, dzmax=dz2)
    KNc, KD, KNt, GNc, GD = tot
    Wc = KNt*KD + GNc*KD - KNc*GD
    okD = bool(KD > 0); okW = bool(Wc < 0)
    print("%spass2: %d cells; <D> > 0: %s; Wc < 0: %s" %
          (tag, c2, okD, okW), flush=True)
    print("%sWc/<D>^2 = %s" % (tag, (Wc/KD**2).str(8)), flush=True)
    return okD and okW


def _subbox(t1_q, t2_q, b1_q, b2_q, dz1, dz2, prec):
    pt = V2(t1_q, b1_q, prec=prec, t_q2=t2_q, b_q2=b2_q)
    tot, c1 = integrate(pt, arb(0), dzmax=dz1)
    E = tot[0]/tot[1]
    eb_num = int(round((float(ball_lo(E))+float(ball_hi(E)))/2*D))
    Eb = arb(eb_num)/D
    tot, c2 = integrate(pt, Eb, dzmax=dz2)
    KNc, KD, KNt, GNc, GD = tot
    Wc = KNt*KD + GNc*KD - KNc*GD
    return bool((Wc < 0) and (KD > 0)), c1 + c2


def certify_box(t1_q, t2_q, b1_q, b2_q, dz1=0.8, dz2=0.15, prec=90,
                db_max=0.02, dt_max=0.005):
    t1 = Fraction(*t1_q); t2 = Fraction(*t2_q)
    b1 = Fraction(*b1_q); b2 = Fraction(*b2_q)
    nb = max(1, int(float(b2 - b1)/db_max) + 1)
    nt = max(1, int(float(t2 - t1)/dt_max) + 1)
    total = 0
    for i in range(nt):
        ta = t1 + (t2 - t1)*i/nt
        tb = t1 + (t2 - t1)*(i+1)/nt
        for j in range(nb):
            ba = b1 + (b2 - b1)*j/nb
            bb = b1 + (b2 - b1)*(j+1)/nb
            ok, c = _subbox((ta.numerator, ta.denominator),
                            (tb.numerator, tb.denominator),
                            (ba.numerator, ba.denominator),
                            (bb.numerator, bb.denominator),
                            dz1, dz2, prec)
            total += c
            print("  sub-box t[%s,%s] b[%s,%s]: %s (%d cells)"
                  % (float(ta), float(tb), float(ba), float(bb),
                     "OK" if ok else "FAIL", c), flush=True)
            if not ok:
                return False, total
    print("BOX CERTIFIED as union of %d sub-boxes; %d cells total"
          % (nt*nb, total), flush=True)
    return True, total


if __name__ == "__main__":
    import time
    t0 = time.time()
    print("=== HARVEST DRIVER (Arb): point -> stability -> 3x3 box ===",
          flush=True)
    ok1 = certify_point((15, 10), (8, 1), dz2=0.15, prec=90, tag="[point] ")
    print("[point] VERDICT:", ok1, " %.0fs" % (time.time()-t0), flush=True)
    t1 = time.time()
    ok2 = certify_point((15, 10), (8, 1), dz2=0.12, prec=120,
                        tag="[stability] ")
    print("[stability] VERDICT:", ok2, " %.0fs" % (time.time()-t1),
          flush=True)
    t2 = time.time()
    ok3, cells = certify_box((15, 10), (151, 100), (8, 1), (805, 100),
                             dz2=0.15, prec=90)
    print("[box 3x3] VERDICT:", ok3, " %.0fs" % (time.time()-t2), flush=True)
    print("HARVEST COMPLETE: point %s / stability %s / box %s"
          % (ok1, ok2, ok3), flush=True)
