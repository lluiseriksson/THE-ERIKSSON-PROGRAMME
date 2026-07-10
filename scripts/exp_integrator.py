"""EXP-FACTORED CENTERED INTEGRATOR - v2b, STANDALONE (the [6,15] machine).

PINNED TARGET (two-pass, centered INSIDE the integration):
  pass 1 (coarse): enclose E = <N>/<D>, pick rational Ebar = mid.
  pass 2: with Nc := N - Ebar*D integrated PER CELL (correlation kept),
    Wc := <N_t><D> + <Nc dK'><D> - <Nc><D dK'>  <  0
  has the sign of E' (exact identity for any constant Ebar; <D> > 0
  certified en passant), where the ALGEBRAIC CANCELLATION
    K * d_t log K = 32 beta^3 c0 c0' (1-P-Q) H(z)   [i1z cancels exactly]
  means the dK'-integrals use G := e^z * 32 b^3 c0 c0' (1-P-Q) B(z)
  and the K-integrals use K = e^z * 2 b A(z), with only TWO correlated
  scaled functions:
    A(z) = e^{-z} I_1(z)/z   -- STRICTLY DECREASING, proved:
      (log A)' = I0/I1 - 1 - 2/z < 0  <=>  I1/I0 > z/(z+2), which follows
      from the classical lower bound I1/I0 >= z/(1+sqrt(1+z^2)) and the
      one-line chain sqrt(1+z^2) <= z+1.  => PURE ENDPOINT enclosure.
    B(z) = e^{-z} H(z), H(z) = (I0 - 2 I1/z)/z^2 (entire, positive
      coefficients) -- enclosed UNCONDITIONALLY by the mixed product
      [e^{-z_hi} H(z_lo), e^{-z_lo} H(z_hi)] (each factor monotone);
      B appears only in the small centered-covariance terms.

CELL GEOMETRY (audit repairs): exact rational centers with denominator
2*D (odd widths handled exactly); the mean-value linearization uses the
EXACT symmetric half-widths h/(2D). Exp factoring: z in zc + gx dx +
gy dy + r with interval gradients (closed forms), gx, gy exact rationals
(their choice affects efficiency only), analytic linear integrals, and
the residual r as an interval.

TRUST BASE: mpmath.iv, self-contained (all helpers vendored). Floats
only in subdivision heuristics and in the CHOICE of Ebar, gx, gy.
"""
from mpmath import iv
from math import factorial

D = 10**6
DZMAX = 0.15


def hull(lo, hi):
    return lo + iv.mpf([0, 1])*(hi - lo)


def exact_pt(e):
    return iv.mpf(e)


def clip0(x):
    lo = exact_pt(x.a)
    if lo < 0:
        return hull(iv.mpf(0), exact_pt(x.b))
    return x


def _series(coef0, step, x):
    """positive series sum with incremental exact steps; x an iv POINT."""
    s = iv.mpf(0)
    term = coef0
    j = 0
    while True:
        s += term
        nxt, r = step(term, j, x)
        if r < iv.mpf(1)/2 and float(nxt.b) < 1e-45*max(float(s.a), 1e-300):
            return s + iv.mpf([0, 1])*(nxt/(1-r))
        term = nxt
        j += 1


def i1_over_z_at(x):
    x2q = (x/2)**2
    def step(t, j, _):
        r = x2q/(iv.mpf(j+1)*iv.mpf(j+2))
        return t*r, r
    return _series(iv.mpf(1)/2, step, x)


def H_at(x):
    x2 = x*x
    def step(t, j, _):
        fac = x2*iv.mpf(j+2)/(iv.mpf(j+1)*iv.mpf(4)*iv.mpf(j+2)*iv.mpf(j+3))
        r = x2/(iv.mpf(4)*iv.mpf(j+1)*iv.mpf(j+3))
        return t*fac, r
    return _series(iv.mpf(1)/8, step, x)


def A_enclose(z):
    """A = e^{-z} I1(z)/z over the z-interval: pure endpoints (A proved
    strictly decreasing)."""
    lo_end = exact_pt(z.b)   # A smallest at z_hi
    hi_end = exact_pt(z.a)
    a_lo = iv.exp(-lo_end)*i1_over_z_at(lo_end)
    a_hi = iv.exp(-hi_end)*i1_over_z_at(hi_end)
    return hull(a_lo, a_hi)


def B_enclose(z):
    """B = e^{-z} H(z): unconditional mixed product bound."""
    zlo = exact_pt(z.a); zhi = exact_pt(z.b)
    lo = iv.exp(-zhi)*H_at(zlo)
    hi = iv.exp(-zlo)*H_at(zhi)
    return hull(lo, hi)


def L_lin(g_num, h_num, den):
    """exact integral of e^{g u}, u in [-h/2, h/2]; g = g_num/den, h = h_num/den."""
    g = iv.mpf(g_num)/den
    h = iv.mpf(h_num)/den
    if abs(g_num) < 10:
        m = iv.exp(abs(g)*h/2)
        return hull(h/m, h*m)
    a = g*h/2
    return (iv.exp(a) - iv.exp(-a))/g


class V2:
    def __init__(self, t_q, b_q, prec=90):
        iv.prec = prec
        self.prec = prec
        self.T = iv.mpf(t_q[0])/iv.mpf(t_q[1])
        self.B = iv.mpf(b_q[0])/iv.mpf(b_q[1])
        self.C = iv.cos(self.T/2)
        self.c0 = iv.cos(self.T/4)
        self.cp = -iv.sin(self.T/4)/4
        self.S2 = iv.sin(self.T/2)
        self.Gpre = 32*self.B**3*self.c0*self.cp   # times (1-P-Q) B(z)

    def geom(self, X, Y):
        S = iv.pi*X; A = iv.pi*Y
        P = iv.sin(S/2)**2
        Q = iv.sin(A/2)**2
        R2 = clip0(4*(self.c0**2*(1-P-Q) + P*Q))
        z = iv.sqrt(clip0(4*self.B**2*R2))
        return S, A, P, Q, R2, z

    def trig(self, S, A, Eb):
        cs = iv.cos(S); ca = iv.cos(A); c2s = iv.cos(2*S); ss = iv.sin(S)
        N = self.C*c2s + ca*(self.C*cs - ss**2)
        Dd = cs + ca
        Nt = -(self.S2/2)*(c2s + ca*cs)
        Nc = N - Eb*Dd          # centered IN-CELL
        return Nc, Dd, Nt

    def cell(self, x1, x2, y1, y2, Eb):
        """returns (KNc, KD, KNt, GNc, GD) integrals over the cell.
        Rational cell: [x1/D, x2/D] x [y1/D, y2/D]."""
        X = hull(iv.mpf(x1)/D, iv.mpf(x2)/D)
        Y = hull(iv.mpf(y1)/D, iv.mpf(y2)/D)
        S, A, P, Q, R2, z = self.geom(X, Y)
        Nc, Dd, Nt = self.trig(S, A, Eb)
        Af = A_enclose(z)
        Bf = B_enclose(z)
        Kslow = 2*self.B*Af
        Gslow = self.Gpre*(1-P-Q)*Bf
        if float(z.b) < 4:
            area = (iv.mpf(x2-x1)/D)*(iv.mpf(y2-y1)/D)*iv.pi**2
            ez = iv.exp(z)
            core = ez*area
            return (core*Kslow*Nc, core*Kslow*Dd, core*Kslow*Nt,
                    core*Gslow*Nc, core*Gslow*Dd)
        # exp branch with EXACT rational center over 2D
        xc2 = x1 + x2          # center = xc2/(2D); half-width = (x2-x1)/(2D)
        yc2 = y1 + y2
        Xc = iv.mpf(xc2)/(2*D); Yc = iv.mpf(yc2)/(2*D)
        _, _, _, _, _, zc = self.geom(Xc, Yc)
        R = iv.sqrt(clip0(R2))
        dR2x = 4*(Q - self.c0**2)*(iv.pi/2)*iv.sin(iv.pi*X)
        dR2y = 4*(P - self.c0**2)*(iv.pi/2)*iv.sin(iv.pi*Y)
        Gx = self.B*dR2x/R
        Gy = self.B*dR2y/R
        gx_num = int(round((float(Gx.a)+float(Gx.b))/2*2*D))
        gy_num = int(round((float(Gy.a)+float(Gy.b))/2*2*D))
        gx = iv.mpf(gx_num)/(2*D); gy = iv.mpf(gy_num)/(2*D)
        hx = x2 - x1; hy = y2 - y1
        r = (Gx-gx)*hull(iv.mpf(-hx)/(2*D), iv.mpf(hx)/(2*D)) \
            + (Gy-gy)*hull(iv.mpf(-hy)/(2*D), iv.mpf(hy)/(2*D))
        Lx = L_lin(gx_num, 2*hx, 2*D)   # h in same denominator 2D
        Ly = L_lin(gy_num, 2*hy, 2*D)
        core = iv.exp(zc)*Lx*Ly*iv.exp(r)*iv.pi**2
        return (core*Kslow*Nc, core*Kslow*Dd, core*Kslow*Nt,
                core*Gslow*Nc, core*Gslow*Dd)


def integrate(pt, Eb, dzmax=DZMAX, hmin=30, max_cells=400000,
              dom=(0, D, 0, D)):
    stack = [dom]
    tot = [iv.mpf(0)]*5
    cells = 0
    while stack:
        x1, x2, y1, y2 = stack.pop()
        X = hull(iv.mpf(x1)/D, iv.mpf(x2)/D)
        Y = hull(iv.mpf(y1)/D, iv.mpf(y2)/D)
        _, _, _, _, _, z = pt.geom(X, Y)
        dz = float(z.b) - float(z.a)
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


def certify_point(t_q, b_q, dz1=0.8, dz2=0.3, prec=90, verbose=True):
    pt = V2(t_q, b_q, prec=prec)
    # pass 1: coarse, Ebar = 0 (uncentered) just for E
    tot, c1 = integrate(pt, iv.mpf(0), dzmax=dz1)
    KNc, KD, KNt, _, _ = tot
    E = KNc/KD   # with Eb=0, KNc = <N>
    eb_num = int(round((float(E.a)+float(E.b))/2*D))
    Eb = iv.mpf(eb_num)/D
    if verbose:
        print("pass1: %d cells, E in %s, Ebar = %d/1e6" %
              (c1, str(E)[:40], eb_num), flush=True)
    # pass 2: centered
    tot, c2 = integrate(pt, Eb, dzmax=dz2)
    KNc, KD, KNt, GNc, GD = tot
    ok_D = KD > 0
    Wc = KNt*KD + GNc*KD - KNc*GD
    if verbose:
        print("pass2: %d cells" % c2, flush=True)
        print("<D> > 0:", ok_D)
        print("Wc/<D>^2 in", str(Wc/KD**2)[:44])
        print("Wc < 0 CERTIFIED:", Wc < 0, flush=True)
    return (Wc < 0) and ok_D


if __name__ == "__main__":
    import sys, time
    dz2 = float(sys.argv[1]) if len(sys.argv) > 1 else 0.3
    t0 = time.time()
    ok = certify_point((15, 10), (8, 1), dz2=dz2)
    print("RESULT:", ok, " %.1fs" % (time.time()-t0))
