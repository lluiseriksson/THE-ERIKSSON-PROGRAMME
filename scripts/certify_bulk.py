"""BULK MACHINE CERTIFICATE (seal session, box 1, machine component).

PINNED STATEMENTS (normalizations of the paper; a_m, b_m the quartic
Bessel coefficients; W = 2(F_A' F_B - F_A F_B')).
  PLAIN MODE  (target for 3 <= beta <= 15):
      W(t, beta) < 0   for all (t, beta) in [1/20, 3.0416] x [box].
  MARGIN MODE (target for beta >= 15, the analytic-handoff form):
      W + sin(t/2) F_B^2 < 0,  i.e.  E' < -(1/4) sin(t/2).
  (The margin form is FALSE near t = pi - 0.10 for beta <= 12 — the truth
   map, notes AG2 — hence the two modes; plain W < 0 is the conjecture
   statement itself on the frozen bulk window.)

METHOD. mpmath.iv, outward rounding. (t, beta) BOXES:
  - beta-boxes: I_m increasing in beta => hull of endpoint enclosures
    (positive series, exact-integer stopping, geometric tails) is
    rigorous, exactly as in certify_thmB.py.
  - t-boxes: T = [t1, t2] as an interval; iv.sin/iv.cos of m*T are
    rigorous range enclosures with argument reduction.
  - Series F_A, F_A', F_B, F_B' summed to M = ceil(beta_hi) + 50 in
    intervals; tails closed with the termwise-exact
    I_{n+1}(x) <= x I_n(x)/(2(n+1)) giving per-index coefficient ratio
    < 1/2 (asserted per box), same shell logic as certify_thmB.py
    (single index here: the coefficient sequences are single-indexed).
  - Certify: upper end of the assembled interval < 0.
  - Adaptive bisection in t per beta-box; beta-boxes on a fixed grid
    subdivided on failure.
COVERAGE CONTRACT (revised by the margin map, seal finding #1): the
machine window is [0.6, 3.0416]. The relative margin of W against the
interval dependency loss scales like ~0.17 t^2 at small t (measured:
5e-4 at t = 0.06, 1.7e-3 at t = 0.1), making [0.05, 0.6] infeasible for
naive interval evaluation (~1e8+ boxes); that strip is assigned to the
EXTENDED 0-BLOCK: e_2 > 0 is proved for ALL beta (Chebyshev corollary),
and its remainder-radius obligation for the machine range becomes 0.6
(the e_4 coefficient bound, same telescoping family - analytic item).
The [pi - 0.10, pi) stub remains the pi-block.

TRUST BASE: mpmath.iv. Floats only in subdivision heuristics.
"""
from mpmath import iv
from math import factorial


def hull(lo, hi):
    return lo + iv.mpf([0, 1])*(hi - lo)


def enc_I_at(m, num, den):
    X = iv.mpf(num)/iv.mpf(2*den)
    s = iv.mpf(0)
    j = 0
    while True:
        t = X**(m+2*j)/(iv.mpf(factorial(j))*iv.mpf(factorial(m+j)))
        s += t
        if (j+1)*(m+j+1) >= 82:   # ratio <= (16/2)^2/82 < 1/2 for x <= 16
            if float(t.b) < 1e-60*max(float(s.a), 1e-300):
                r = (X*X)/(iv.mpf(j+1)*iv.mpf(m+j+1))
                return s + iv.mpf([0, 1])*(t*r/(1-r))
        j += 1


class BetaBox:
    """Bessel/coefficient data shared by all t-boxes of one beta-box."""
    def __init__(self, r1, r2, prec=110):
        iv.prec = prec
        self.prec = prec
        bhi = r2[0]/r2[1]
        self.M = int(bhi) + 50
        M = self.M
        I = [hull(enc_I_at(m, *r1), enc_I_at(m, *r2)) for m in range(M+3)]
        self.a = [iv.mpf(0)]*(M+2)
        self.b = [iv.mpf(0)]*(M+2)
        for m in range(1, M+2):
            self.a[m] = I[m]**2*((m-1)*I[m-1]**2 + (m+1)*I[m+1]**2)
            self.b[m] = iv.mpf(m)*I[m]**4
        # tail ratio: I_{n+1} <= x I_n/(2(n+1)) termwise-exact; each unit
        # increase of m multiplies a_m, b_m by <= (x_hi/(2M))^4 * poly;
        # assert < 1/2 and precompute geometric tail majorants.
        X_hi = iv.mpf(r2[0])/iv.mpf(r2[1])
        r = (X_hi/(2*iv.mpf(M)))**4 * (iv.mpf(M+1)/iv.mpf(M))**2
        assert r < iv.mpf(1)/2, "coefficient tail ratio failed"
        gA = self.a[M+1]/(1-r)          # sum_{m>M} a_m <= a_{M+1}/(1-r)
        gB = self.b[M+1]/(1-r)
        # m-weighted tails: sum m a_m <= (M+1) a_{M+1} sum ((k+M+1)/(M+1)) r^k
        #                <= (M+1) a_{M+1} * (1/(1-r) + r/(1-r)^2 /(M+1)) — majorize crudely by 2(M+1)a_{M+1}/(1-r)^2
        gAw = 2*iv.mpf(M+1)*self.a[M+1]/(1-r)**2
        gBw = 2*iv.mpf(M+1)*self.b[M+1]/(1-r)**2
        self.tails = (gA, gB, gAw, gBw)

    def G(self, t1q, t2q, margin=False):
        """interval for W (+ margin term) over the t-box [t1q, t2q] (rationals)."""
        iv.prec = self.prec
        T = hull(iv.mpf(t1q[0])/iv.mpf(t1q[1]), iv.mpf(t2q[0])/iv.mpf(t2q[1]))
        M = self.M
        FA = iv.mpf(0); FB = iv.mpf(0); FAp = iv.mpf(0); FBp = iv.mpf(0)
        for m in range(1, M+1):
            sm = iv.sin(iv.mpf(m)*T); cm = iv.cos(iv.mpf(m)*T)
            FA += self.a[m]*sm
            FB += self.b[m]*sm
            FAp += iv.mpf(m)*self.a[m]*cm
            FBp += iv.mpf(m)*self.b[m]*cm
        gA, gB, gAw, gBw = self.tails
        pm = iv.mpf([-1, 1])
        FA += pm*gA; FB += pm*gB; FAp += pm*gAw; FBp += pm*gBw
        W = 2*(FAp*FB - FA*FBp)
        if margin:
            W = W + iv.sin(T/2)*FB**2
        return W


def cover_t(bb, t_lo, t_hi, margin=False, verbose=False):
    """adaptive t-cover of [t_lo, t_hi] for one BetaBox; returns box count."""
    D = 10**6
    count = 0
    stack = [(t_lo, t_hi)]
    while stack:
        x1, x2 = stack.pop()
        G = bb.G((int(x1*D), D), (int(x2*D)+1, D), margin=margin)
        if G < 0:
            count += 1
            if verbose:
                print("    t-box [%.4f, %.4f] ok" % (x1, x2), flush=True)
        else:
            if x2 - x1 < 5e-5:
                raise RuntimeError("bulk failure near t=%.5f" % x1)
            mid = (x1+x2)/2
            stack.append((mid, x2)); stack.append((x1, mid))
    return count


CWIN = 1.5   # moving pi-boundary: machine certifies t <= pi - CWIN/beta
             # (the mirror window has width ~sqrt(2)/beta; the pi-block's
             # quadratic regime is valid to ~2/beta with retention ~0.89,
             # so CWIN = 1.5 sits inside the splice band
             # C_mirror <= C <= C_quad for the whole machine range)


def cover(b_lo, b_hi, db, t_lo=0.6, t_hi=None, margin=False, prec=110):
    from math import pi as PI_F
    D = 10**6
    total = 0
    b = b_lo
    while b < b_hi - 1e-12:
        b2 = min(b + db, b_hi)
        try:
            bb = BetaBox((int(b*D), D), (int(b2*D)+1, D), prec=prec)
            th = (PI_F - CWIN/b) if t_hi is None else t_hi   # beta-dependent
            n = cover_t(bb, t_lo, th, margin=margin)
            total += n
            print("beta-box [%.4f, %.4f]: %d t-boxes (%s)" %
                  (b, b2, n, "margin" if margin else "plain"), flush=True)
            b = b2
        except RuntimeError:
            if db < 1e-4:
                raise
            db = db/2
            print("  narrowing beta step to %.5f at beta=%.4f" % (db, b),
                  flush=True)
    return total


if __name__ == "__main__":
    import sys
    b1 = float(sys.argv[1]); b2 = float(sys.argv[2])
    db = float(sys.argv[3]) if len(sys.argv) > 3 else 0.25
    mode = sys.argv[4] if len(sys.argv) > 4 else "plain"
    total = cover(b1, b2, db, margin=(mode == "margin"))
    print("CERTIFIED (%s): W%s < 0 on [0.6, pi-%.2f/beta] x [%g, %g]; %d boxes"
          % (mode, "" if mode == "plain" else " + sin(t/2)F_B^2", 1.5, b1, b2, total),
          flush=True)
