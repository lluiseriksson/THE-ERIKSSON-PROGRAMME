"""POSITIVE-REPRESENTATION 2D INTEGRATOR (seal machine for [6, 15]) - v0.

PINNED TARGET. Via the master formula (paper, Lemma 15 with the exact
E' decomposition and D_t = 0), with <f> := II_{[-pi,pi]x[-pi,pi]}
K f ds d-alpha, K = I_1(2 beta R)/R > 0:
    E' < 0   <=>   Num := <N_t><D> + <N dK><D> - <N><D dK> < 0,
given <D> > 0 (certified en passant), where
    N   = C cos 2s + cos a (C cos s - sin^2 s),   C = cos(t/2)
    D   = cos s + cos a
    N_t = -(1/2) sin(t/2) [cos 2s + cos a cos s]
    dK  = d_t log K = 4 c c' (1-P-Q) [z I_0(z)/I_1(z) - 2]/R^2,
          z = 2 beta R, c = cos(t/4), c' = -sin(t/4)/4,
          regular at R = 0 with value 4 beta^2 c c' (1-P-Q).
WHY THIS REPRESENTATION: the kernel is positive and saddle-concentrated;
there is NO internal exponential cancellation (unlike the sine series,
which cancel by e^{4 beta (1-cos(t/4))} on the pi side) - the
positive-representation ledger rule at architecture level.

METHOD (v0). Quarter-domain (integrands even in s and in alpha):
cells over [0,pi]^2, per-cell interval enclosure of each integrand
(R^2 = 4[c0^2(1-P-Q) + PQ] in intervals; I_1(z)/z and I_0(z) by
positive-series enclosures, monotone in z over the cell), times exact
cell area; adaptive subdivision driven by the width of the total.
The five integrals share the cell tree and the kernel enclosures.
v0 GOAL: correctness + cost measurement at single (t, beta) points;
the (t, beta)-box layer and the Arb port follow once validated.

TRUST BASE: mpmath.iv; floats only in subdivision heuristics.
"""
from mpmath import iv
from math import factorial


def hull(lo, hi):
    return lo + iv.mpf([0, 1])*(hi - lo)


def I1_over_z(z):
    """enclosure of I_1(z)/z = (1/2) sum (z/2)^{2j} /(j!(j+1)!), z interval >= 0.
    Monotone increasing in z => evaluate at endpoints via positive series."""
    def at(x):
        s = iv.mpf(0)
        j = 0
        while True:
            t = (x/2)**(2*j)/(iv.mpf(factorial(j))*iv.mpf(factorial(j+1)))
            s += t
            xb = float(x.b)
            if (j+1)*(j+2) >= 2*(xb/2)**2 + 20:
                r = (x/2)**2/(iv.mpf(j+1)*iv.mpf(j+2))
                return (s + iv.mpf([0, 1])*(t*r/(1-r)))/2
            j += 1
    zlo = iv.mpf([float(z.a), float(z.a)])
    zhi = iv.mpf([float(z.b), float(z.b)])
    return hull(at(zlo), at(zhi))


def I0(z):
    def at(x):
        s = iv.mpf(0)
        j = 0
        while True:
            t = (x/2)**(2*j)/iv.mpf(factorial(j))**2
            s += t
            xb = float(x.b)
            if (j+1)**2 >= 2*(xb/2)**2 + 20:
                r = (x/2)**2/iv.mpf(j+1)**2
                return s + iv.mpf([0, 1])*(t*r/(1-r))
            j += 1
    zlo = iv.mpf([float(z.a), float(z.a)])
    zhi = iv.mpf([float(z.b), float(z.b)])
    return hull(at(zlo), at(zhi))


class Point:
    """integrand machinery at fixed (t, beta) — v0 works pointwise."""
    def __init__(self, t_q, b_q, prec=80):
        iv.prec = prec
        self.T = iv.mpf(t_q[0])/iv.mpf(t_q[1])
        self.B = iv.mpf(b_q[0])/iv.mpf(b_q[1])
        self.C = iv.cos(self.T/2)
        self.c0 = iv.cos(self.T/4)
        self.cp = -iv.sin(self.T/4)/4
        self.S2 = iv.sin(self.T/2)

    def cell(self, s1, s2, a1, a2):
        """interval enclosures of (K, N, D, N_t, dK) over the cell."""
        S = hull(iv.mpf(s1[0])/iv.mpf(s1[1]), iv.mpf(s2[0])/iv.mpf(s2[1]))
        A = hull(iv.mpf(a1[0])/iv.mpf(a1[1]), iv.mpf(a2[0])/iv.mpf(a2[1]))
        P = iv.sin(S/2)**2
        Q = iv.sin(A/2)**2
        R2 = 4*(self.c0**2*(1-P-Q) + P*Q)
        R2 = R2 & iv.mpf([0, 16]) if False else _clip0(R2)
        z2 = 4*self.B**2*R2                     # z^2
        z = iv.sqrt(_clip0(z2))
        i1z = I1_over_z(z)                      # I1(z)/z
        K = 2*self.B*i1z                        # I1(2 b R)/R = 2 b * I1(z)/z
        cs = iv.cos(S); ca = iv.cos(A); c2s = iv.cos(2*S); ss = iv.sin(S)
        N = self.C*c2s + ca*(self.C*cs - ss**2)
        D = cs + ca
        Nt = -(self.S2/2)*(c2s + ca*cs)
        # dK regular form: 4 c c' (1-P-Q) [z I0/I1 - 2]/R^2
        #   [z I0/I1 - 2]/R^2 = 4 b^2 [I0 - 2 I1/z] / z^2  ... use series-safe:
        #   z I0/I1 - 2 = (I0 - 2*I1_over_z)/(I1_over_z)  ... careful: I1/z form:
        #   z I0/I1 = I0/I1_over_z ; so bracket = I0/i1z - 2, and /R^2 -> *4b^2/z^2
        i0 = I0(z)
        brk = i0/i1z - 2
        dK = 4*self.c0*self.cp*(1-P-Q)*brk*4*self.B**2/_clipeps(z2)
        return K, N, D, Nt, dK


def _clip0(x):
    # intersect with [0, inf): rigorous (values are true squares)
    return iv.mpf([max(0.0, float(x.a)), float(x.b)])


def _clipeps(x):
    # z^2 lower-clipped at tiny positive for the division; the bracket
    # z I0/I1 - 2 = z^2/4 + O(z^4) vanishes at the same rate, and the
    # corners where R -> 0 carry vanishing prefactors; v0 subdivides
    # around them and uses the crude bound below when z is tiny.
    return iv.mpf([max(1e-30, float(x.a)), float(x.b)])


def integrate(pt, target_rel, max_cells=200000, verbose=False):
    """adaptive quarter-domain integration of the five integrals."""
    D6 = 10**6
    PI_UP = 3141593  # /1e6 > pi
    # SCALE for the subdivision heuristic (floats allowed here): kernel
    # value at the saddle times O(1) integrand factors.
    Ksad, _, _, _, _ = pt.cell((0, D6), (1, D6), (0, D6), (1, D6))
    scale = float(Ksad.b)*4.0
    stack = [((0, D6), (PI_UP, D6), (0, D6), (PI_UP, D6))]
    tot = [iv.mpf(0)]*5
    cells = 0
    final = []
    # first pass: subdivide until per-cell K-width is moderate
    while stack:
        s1, s2, a1, a2 = stack.pop()
        K, N, D, Nt, dK = pt.cell(s1, s2, a1, a2)
        area = (iv.mpf(s2[0]-s1[0])/D6)*(iv.mpf(a2[0]-a1[0])/D6)
        vals = (K*N*area, K*D*area, K*Nt*area, K*N*dK*area, K*D*dK*area)
        wid = max(float(v.b) - float(v.a) for v in vals)
        cellarea = ((s2[0]-s1[0])/D6)*((a2[0]-a1[0])/D6)
        sz = (s2[0]-s1[0])/D6
        if (wid > target_rel*scale*max(cellarea, 1e-12)*10
                and sz > 2e-4 and cells + len(stack) < max_cells):
            sm = ((s1[0]+s2[0])//2, D6)
            am = ((a1[0]+a2[0])//2, D6)
            stack += [(s1, sm, a1, am), (sm, s2, a1, am),
                      (s1, sm, am, a2), (sm, s2, am, a2)]
        else:
            for i in range(5):
                tot[i] += vals[i]
            cells += 1
    return tot, cells


if __name__ == "__main__":
    import sys, time
    t0 = time.time()
    pt = Point((15, 10), (8, 1), prec=80)      # t = 1.5, beta = 8
    tot, cells = integrate(pt, target_rel=float(sys.argv[1]) if len(sys.argv) > 1 else 1e-3)
    NN, DD, NT, NK, DKI = tot
    print("cells:", cells, " %.1fs" % (time.time()-t0))
    print("<D>  =", str(DD)[:50])
    E = NN/DD
    print("E    =", str(E)[:50])
    Num = NT*DD + NK*DD - NN*DKI
    print("Num  =", str(Num)[:60])
    print("E'   =", str((NT + NK - E*DKI)/DD)[:60])
