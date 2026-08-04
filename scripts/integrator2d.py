"""POSITIVE-REPRESENTATION 2D INTEGRATOR (seal machine for [6, 15]) - v1a.

PINNED TARGET (no quotients -- the protocol instruction): with
<f> := II K f over the quarter domain (doubled by evenness in s and in
alpha), K = I_1(2 beta R)/R > 0:
    Wtil := <N_t><D> + <N dK><D> - <N><D dK>  <  0
has the sign of E' (given <D> > 0, certified en passant). Five interval
integrals, then products and sums -- no division anywhere.

RIGOR REPAIRS (v0 -> v1a, all four audit blockers):
1. dK REGULAR EVERYWHERE, no clipped denominators:
       dK = 16 beta^2 c c' (1-P-Q) * H(z) / (I_1(z)/z),
   H(z) = (I_0(z) - 2 I_1(z)/z)/z^2
        = sum_{j>=0} (j+1) z^{2j} / (4^{j+1} (j+1)! (j+2)!),
   an entire positive-coefficient series (monotone in z), enclosed like
   I_1(z)/z; the denominator I_1(z)/z >= 1/2 > 0 everywhere.
2. NO FLOAT ROUND-TRIPS in enclosures: interval endpoints are reused as
   exact binary values (iv.mpf(x.a)); floats remain ONLY in subdivision
   heuristics.
3. EXACT DOMAIN: cells live in (x, y) in [0,1]^2 with s = pi x,
   alpha = pi y; the factor pi^2 (Jacobian) and all angles carry iv.pi.
   No over-covered square for a signed integrand.
4. (paper-side blocker fixed in the manuscript migration.)

TRUST BASE: mpmath.iv. v1a is the rigorous point evaluator; the
second-order cell layer, the (t,beta)-box layer and the Arb port are v2.
"""
from mpmath import iv
from math import factorial


def hull(lo, hi):
    return lo + iv.mpf([0, 1])*(hi - lo)


def exact_pt(e):
    """iv number equal to an interval endpoint (exact binary reuse)."""
    return iv.mpf(e)


def i1_over_z(z):
    """I_1(z)/z = sum_j (z/2)^{2j} / (j!(j+1)!) / 2 ; >= 1/2, monotone."""
    def at(x):
        s = iv.mpf(0)
        j = 0
        term = iv.mpf(1)/2
        x2q = (x/2)**2
        while True:
            s += term
            nxt = term*x2q/(iv.mpf(j+1)*iv.mpf(j+2))
            r = x2q/(iv.mpf(j+1)*iv.mpf(j+2))
            if r < iv.mpf(1)/2 and float(nxt.b) < 1e-45*max(float(s.a), 1e-300):
                return s + iv.mpf([0, 1])*(nxt/(1-r))
            term = nxt
            j += 1
    return hull(at(exact_pt(z.a)), at(exact_pt(z.b)))


def i0(z):
    def at(x):
        s = iv.mpf(0)
        j = 0
        term = iv.mpf(1)
        x2q = (x/2)**2
        while True:
            s += term
            nxt = term*x2q/iv.mpf(j+1)**2
            r = x2q/iv.mpf(j+1)**2
            if r < iv.mpf(1)/2 and float(nxt.b) < 1e-45*max(float(s.a), 1e-300):
                return s + iv.mpf([0, 1])*(nxt/(1-r))
            term = nxt
            j += 1
    return hull(at(exact_pt(z.a)), at(exact_pt(z.b)))


def hseries(z):
    """H(z) = sum_j (j+1) z^{2j} / (4^{j+1} (j+1)! (j+2)!), positive, monotone."""
    def at(x):
        s = iv.mpf(0)
        j = 0
        term = iv.mpf(1)/8          # j=0: 1/(4*1*2)
        x2 = x*x
        while True:
            s += term
            # term_{j+1}/term_j = x^2 (j+2)^2? compute exactly:
            #   (j+2)/(j+1) * 1/4 * 1/((j+2)(j+3)) * x^2
            fac = x2*iv.mpf(j+2)/(iv.mpf(j+1)*iv.mpf(4)*iv.mpf(j+2)*iv.mpf(j+3))
            nxt = term*fac
            r = x2/(iv.mpf(4)*iv.mpf(j+1)*iv.mpf(j+3))
            if r < iv.mpf(1)/2 and float(nxt.b) < 1e-45*max(float(s.a), 1e-300):
                return s + iv.mpf([0, 1])*(nxt/(1-r))
            term = nxt
            j += 1
    return hull(at(exact_pt(z.a)), at(exact_pt(z.b)))


def clip0(x):
    """rigorous intersection with [0, inf) using exact endpoints."""
    lo = exact_pt(x.a)
    if lo < 0:
        return hull(iv.mpf(0), exact_pt(x.b))
    return x


class Point:
    def __init__(self, t_q, b_q, prec=80):
        iv.prec = prec
        self.prec = prec
        self.T = iv.mpf(t_q[0])/iv.mpf(t_q[1])
        self.B = iv.mpf(b_q[0])/iv.mpf(b_q[1])
        self.C = iv.cos(self.T/2)
        self.c0 = iv.cos(self.T/4)
        self.cp = -iv.sin(self.T/4)/4
        self.S2 = iv.sin(self.T/2)

    def cell(self, x1, x2, y1, y2, D6=10**6):
        """(x, y) in [0,1]^2 rationals; s = pi x, alpha = pi y."""
        X = hull(iv.mpf(x1)/D6, iv.mpf(x2)/D6)
        Y = hull(iv.mpf(y1)/D6, iv.mpf(y2)/D6)
        S = iv.pi*X
        A = iv.pi*Y
        P = iv.sin(S/2)**2
        Q = iv.sin(A/2)**2
        R2 = clip0(4*(self.c0**2*(1-P-Q) + P*Q))
        z = iv.sqrt(clip0(4*self.B**2*R2))
        i1z = i1_over_z(z)
        K = 2*self.B*i1z
        cs = iv.cos(S); ca = iv.cos(A); c2s = iv.cos(2*S); ss = iv.sin(S)
        N = self.C*c2s + ca*(self.C*cs - ss**2)
        D = cs + ca
        Nt = -(self.S2/2)*(c2s + ca*cs)
        dK = 16*self.B**2*self.c0*self.cp*(1-P-Q)*hseries(z)/i1z
        return K, N, D, Nt, dK


def integrate(pt, target_rel=1e-3, max_cells=400000):
    D6 = 10**6
    Ksad, _, _, _, _ = pt.cell(0, 1, 0, 1)
    scale = float(Ksad.b)
    stack = [(0, D6, 0, D6)]
    tot = [iv.mpf(0)]*5
    cells = 0
    JAC = iv.pi**2  # Jacobian of (s,alpha) = (pi x, pi y)
    while stack:
        x1, x2, y1, y2 = stack.pop()
        K, N, D, Nt, dK = pt.cell(x1, x2, y1, y2)
        area = (iv.mpf(x2-x1)/D6)*(iv.mpf(y2-y1)/D6)*JAC
        vals = (K*N*area, K*D*area, K*Nt*area, K*N*dK*area, K*D*dK*area)
        wid = max(float(v.b) - float(v.a) for v in vals)
        cellarea = ((x2-x1)/D6)*((y2-y1)/D6)
        if (wid > target_rel*scale*max(cellarea, 1e-12)*98.7
                and (x2-x1) > 60 and cells + len(stack) < max_cells):
            xm = (x1+x2)//2; ym = (y1+y2)//2
            stack += [(x1, xm, y1, ym), (xm, x2, y1, ym),
                      (x1, xm, ym, y2), (xm, x2, ym, y2)]
        else:
            for i in range(5):
                tot[i] += vals[i]
            cells += 1
    return tot, cells


if __name__ == "__main__":
    import sys, time
    tgt = float(sys.argv[1]) if len(sys.argv) > 1 else 1e-3
    t0 = time.time()
    pt = Point((15, 10), (8, 1), prec=80)
    tot, cells = integrate(pt, target_rel=tgt)
    NN, DD, NT, NK, DKI = tot
    print("cells:", cells, " %.1fs" % (time.time()-t0), flush=True)
    print("<D>  > 0:", DD > 0, "  ", str(DD)[:44])
    print("E in", str(NN/DD)[:44], " (truth ~0.566)")
    Wtil = NT*DD + NK*DD - NN*DKI
    print("Wtil =", str(Wtil)[:56])
    print("Wtil < 0 CERTIFIED:", Wtil < 0)
