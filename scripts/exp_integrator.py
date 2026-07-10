"""EXP-FACTORED POSITIVE INTEGRATOR (candidate B) - v2 of the [6,15] machine.

TARGET (centered, the protocol's no-quotient form with the desk's
centering identity -- exact for any constant Ebar):
    Wc := <N_t><D> + <(N - Ebar D) dK><D> - (<N> - Ebar<D>)<D dK>  <  0
has the sign of E' (given <D> > 0). Ebar is a rational midpoint of a
first-pass enclosure of E; the identity kills the ~100x cancellation
between the two covariance products.

ALGORITHM (per cell, z = 2 beta R):
  plain branch (z_hi < 4): v1a-style interval enclosure (e^z bounded).
  exp branch: factor the exponential growth through the MEAN-VALUE
  linearization of z over the cell:
      z(x,y) in z_c + gx dx + gy dy + r,
      gx, gy exact rationals near mid(grad z); r in
      (Gx-gx)[-hx/2,hx/2] + (Gy-gy)[-hy/2,hy/2], with Gx, Gy interval
      gradients over the cell (closed forms from R^2 = 4[c0^2(1-P-Q)+PQ]);
  then  II e^z F = e^{z_c} * L(gx,hx) * L(gy,hy) * hull(e^r * F_slow),
  where L(g,h) = (e^{g h/2} - e^{-g h/2})/g is the EXACT linear integral
  (small-|g| branch: crude two-sided bound), and
      F_slow = e^{-z} I_1(z)/z * (trig factors) * 2 beta * JAC
  is enclosed with the cell's z-interval kept NARROW by the subdivision
  discipline dz <= DZMAX (so e^{-z}-type intervals stay tight).
  dK uses the regular H(z) series; the ratio H/i1z is enclosed through
  the same narrow z-interval.
TRUST BASE: mpmath.iv; floats only pick gx, gy and drive subdivision --
the decomposition is rigorous for ANY choice of the rationals gx, gy.
"""
from mpmath import iv
from integrator2d import hull, exact_pt, i1_over_z, i0, hseries, clip0

DZMAX = 0.15
D6 = 10**6


def L_lin(g_num, h_num):
    """exact integral of e^{g u} over u in [-h/2, h/2]; g, h rationals /D6."""
    g = iv.mpf(g_num)/D6
    h = iv.mpf(h_num)/D6
    if abs(g_num) < 10:   # |g| < 1e-5: crude two-sided bound
        m = iv.exp(abs(g)*h/2)
        return hull(h/m, h*m)
    a = g*h/2
    return (iv.exp(a) - iv.exp(-a))/g


class ExpPoint:
    def __init__(self, t_q, b_q, prec=80):
        iv.prec = prec
        self.prec = prec
        self.T = iv.mpf(t_q[0])/iv.mpf(t_q[1])
        self.B = iv.mpf(b_q[0])/iv.mpf(b_q[1])
        self.C = iv.cos(self.T/2)
        self.c0 = iv.cos(self.T/4)
        self.cp = -iv.sin(self.T/4)/4
        self.S2 = iv.sin(self.T/2)

    def geom(self, X, Y):
        S = iv.pi*X; A = iv.pi*Y
        P = iv.sin(S/2)**2
        Q = iv.sin(A/2)**2
        R2 = clip0(4*(self.c0**2*(1-P-Q) + P*Q))
        z = iv.sqrt(clip0(4*self.B**2*R2))
        return S, A, P, Q, R2, z

    def trig(self, S, A):
        cs = iv.cos(S); ca = iv.cos(A); c2s = iv.cos(2*S); ss = iv.sin(S)
        N = self.C*c2s + ca*(self.C*cs - ss**2)
        D = cs + ca
        Nt = -(self.S2/2)*(c2s + ca*cs)
        return N, D, Nt

    def cell_plain(self, x1, x2, y1, y2):
        X = hull(iv.mpf(x1)/D6, iv.mpf(x2)/D6)
        Y = hull(iv.mpf(y1)/D6, iv.mpf(y2)/D6)
        S, A, P, Q, R2, z = self.geom(X, Y)
        i1z = i1_over_z(z)
        K = 2*self.B*i1z
        N, D, Nt = self.trig(S, A)
        dK = 16*self.B**2*self.c0*self.cp*(1-P-Q)*hseries(z)/i1z
        area = (iv.mpf(x2-x1)/D6)*(iv.mpf(y2-y1)/D6)*iv.pi**2
        return (K*N*area, K*D*area, K*Nt*area, K*N*dK*area, K*D*dK*area)

    def cell_exp(self, x1, x2, y1, y2):
        X = hull(iv.mpf(x1)/D6, iv.mpf(x2)/D6)
        Y = hull(iv.mpf(y1)/D6, iv.mpf(y2)/D6)
        S, A, P, Q, R2, z = self.geom(X, Y)
        # center point (tight)
        xc = (x1+x2)//2; yc = (y1+y2)//2
        Xc = iv.mpf(xc)/D6; Yc = iv.mpf(yc)/D6
        Sc, Ac, Pc, Qc, R2c, zc = self.geom(Xc, Yc)
        # interval gradients over the cell:
        #   dz/dx = beta * dR2/dx / R,  dR2/dx = 4(Q - c0^2) (pi/2) sin(pi x)
        R = iv.sqrt(clip0(R2))
        dR2x = 4*(Q - self.c0**2)*(iv.pi/2)*iv.sin(iv.pi*X)
        dR2y = 4*(P - self.c0**2)*(iv.pi/2)*iv.sin(iv.pi*Y)
        Gx = self.B*dR2x/R
        Gy = self.B*dR2y/R
        gx_num = int(round((float(Gx.a)+float(Gx.b))/2*D6))
        gy_num = int(round((float(Gy.a)+float(Gy.b))/2*D6))
        gx = iv.mpf(gx_num)/D6; gy = iv.mpf(gy_num)/D6
        hx = x2-x1; hy = y2-y1
        r = (Gx-gx)*hull(iv.mpf(-hx)/(2*D6), iv.mpf(hx)/(2*D6)) \
            + (Gy-gy)*hull(iv.mpf(-hy)/(2*D6), iv.mpf(hy)/(2*D6))
        Lx = L_lin(gx_num, hx); Ly = L_lin(gy_num, hy)
        core = iv.exp(zc)*Lx*Ly*iv.exp(r)*iv.pi**2
        # slow factors over the cell (narrow z-interval by discipline)
        ei1z = i1_over_z(z)*iv.exp(-z)
        N, D, Nt = self.trig(S, A)
        Kslow = 2*self.B*ei1z
        ratio = hseries(z)/i1_over_z(z)      # H/i1z, same-z narrow interval
        dK = 16*self.B**2*self.c0*self.cp*(1-P-Q)*ratio
        return (core*Kslow*N, core*Kslow*D, core*Kslow*Nt,
                core*Kslow*N*dK, core*Kslow*D*dK)


def integrate(pt, max_cells=300000, dzmax=DZMAX, hmin=30):
    stack = [(0, D6, 0, D6)]
    tot = [iv.mpf(0)]*5
    cells = 0
    while stack:
        x1, x2, y1, y2 = stack.pop()
        X = hull(iv.mpf(x1)/D6, iv.mpf(x2)/D6)
        Y = hull(iv.mpf(y1)/D6, iv.mpf(y2)/D6)
        _, _, _, _, _, z = pt.geom(X, Y)
        dz = float(z.b) - float(z.a)
        if dz > dzmax and (x2-x1) > hmin and cells + len(stack) < max_cells:
            xm = (x1+x2)//2; ym = (y1+y2)//2
            stack += [(x1, xm, y1, ym), (xm, x2, y1, ym),
                      (x1, xm, ym, y2), (xm, x2, ym, y2)]
            continue
        vals = (pt.cell_plain(x1, x2, y1, y2) if float(z.b) < 4
                else pt.cell_exp(x1, x2, y1, y2))
        for i in range(5):
            tot[i] += vals[i]
        cells += 1
    return tot, cells


if __name__ == "__main__":
    import sys, time
    dz = float(sys.argv[1]) if len(sys.argv) > 1 else DZMAX
    t0 = time.time()
    pt = ExpPoint((15, 10), (8, 1), prec=90)
    tot, cells = integrate(pt, dzmax=dz)
    NN, DD, NT, NK, DKI = tot
    print("cells:", cells, " %.1fs" % (time.time()-t0), flush=True)
    print("<D> > 0:", DD > 0)
    E = NN/DD
    print("E in", str(E)[:46], " (truth ~0.566)")
    # centered target with rational Ebar = midpoint of E-enclosure
    eb = int(round((float(E.a)+float(E.b))/2*D6))
    Eb = iv.mpf(eb)/D6
    Wc = NT*DD + (NK - Eb*DKI)*DD - (NN - Eb*DD)*DKI
    print("Wc  =", str(Wc)[:56])
    print("Wc/<D>^2 in", str(Wc/DD**2)[:46], " (truth E' ~ -0.34)")
    print("Wc < 0 CERTIFIED:", Wc < 0)
