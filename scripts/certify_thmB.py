"""CERTIFICATE for Theorem B (the finite certified computation).

PINNED STATEMENT. For beta in [1/20, 3] and all t in (0, pi):
    W(t) = sum_{m<n} c_mn T_mn(t) < 0,
where c_mn = a_m b_n - a_n b_m (< 0 for all m < n by the phi-lemma,
exact), T_mn(t) = (m-n) sin((m+n)t) + (m+n) sin((n-m)t), and
a_m = I_m^2[(m-1)I_{m-1}^2 + (m+1)I_{m+1}^2], b_m = m I_m^4.

EXACT SKELETON (every analytic ingredient is a proved identity or a
three-line inequality; proofs in the paper, Sec. Theorem B):
  T_{12} = 4 sin^3 t;   T_{13} = 16 sin^3 t cos t;   T_{24} = 8 sin^3(2t),
  so |T_13| <= 16 sin^3 t and |T_24| <= 64 sin^3 t;
  T_{m,m+1} >= 0 for all m  (|sin qt| <= q sin t, classical);
  |T_mn| <= (pi^3/48) p q (q^2+p^2) sin^3 t, p = n-m, q = n+m
  (T and T', T'' vanish at 0 and pi; |T'''| <= p q (q^2 + p^2);
   sin t >= (2/pi) min(t, pi-t)).
Hence, pointwise in t in (0, pi),
  W / sin^3 t <= Crit(beta) :=
    -4|c_12| + 16|c_13| + 64|c_24|
    + (pi^3/48) * sum over p >= 2, (m,n) not in {(1,3),(2,4)}
      of p q (q^2+p^2) |c_mn|
(adjacent pairs m >= 2 are dropped: c < 0, T >= 0).
CLAIM CERTIFIED HERE: Crit(beta) < 0 for all beta in [1/20, 3].

METHOD. mpmath.iv, outward rounding. beta-BOXES: I_m(beta) is increasing
in beta (positive series termwise), so over [b1, b2] the hull
[lower encl. at b1, upper encl. at b2] is a rigorous enclosure; endpoint
enclosures by the positive series with an exact-integer stopping rule and
geometric tails. Crit is evaluated in intervals; the box certifies when
the interval upper end is < 0 (this uses the lower end of |c_12|, whose
positivity -- i.e. c_12 < 0 -- is certified per box en passant, and upper
ends of all other |c_mn|). Cutoff M = 60; the TAIL IS COMPUTED IN
INTERVALS: pairs with max index in (M, M+24] are summed exactly, and the
remainder beyond M+24 is closed geometrically with a FORMALLY DERIVED
per-index ratio: the termwise inequality I_{n+1}(x) <= x I_n(x)/(2(n+1))
(exact from the series: 1/(n+1+j)! <= 1/((n+1)(n+j)!)) makes each unit
increase of the max index multiply the four-Bessel products by at most
(x/(2(n+1)))^4 while the weight grows by at most ((q+1)/q)^4 (n+1)/n;
the resulting ratio bound is computed in intervals per box and ASSERTED
< 1/2 before the closure sum(r^j) <= r/(1-r) is applied. Adaptive
bisection covers [1/20, 3]; floats appear only in subdivision
heuristics, never in enclosures. For beta in (0, 1/20] the paper's
small-beta lemma (exact) takes over.
"""
from mpmath import iv
from math import factorial

MT = 60


def hull(lo, hi):
    """iv number containing [lo.a, hi.b] for iv numbers lo <= hi."""
    return lo + iv.mpf([0, 1])*(hi - lo)


def enc_I_at(m, num, den):
    """enclosure of I_m(num/den) by the positive series + geometric tail."""
    X = iv.mpf(num)/iv.mpf(2*den)   # x/2, exact rational
    s = iv.mpf(0)
    j = 0
    while True:
        t = X**(m+2*j)/(iv.mpf(factorial(j))*iv.mpf(factorial(m+j)))
        s += t
        if (j+1)*(m+j+1) >= 20:   # exact test: term ratio <= (3/2)^2/20 < 1/2 (x <= 3)
            if float(t.b) < 1e-60*max(float(s.a), 1e-300):
                r = (X*X)/(iv.mpf(j+1)*iv.mpf(m+j+1))
                return s + iv.mpf([0, 1])*(t*r/(1-r))
        j += 1


def crit_box(r1, r2, prec=100):
    """interval upper bound of Crit over the beta-box [r1, r2] (rationals)."""
    iv.prec = prec
    EX = 24   # tail extension: pairs with max index in (MT, MT+EX]
    I = [hull(enc_I_at(m, *r1), enc_I_at(m, *r2)) for m in range(MT+EX+3)]
    a = [iv.mpf(0)]*(MT+EX+2)
    b = [iv.mpf(0)]*(MT+EX+2)
    for m in range(1, MT+EX+2):
        a[m] = I[m]**2*((m-1)*I[m-1]**2 + (m+1)*I[m+1]**2)
        b[m] = iv.mpf(m)*I[m]**4
    def cabs(m, n):
        return a[n]*b[m] - a[m]*b[n]
    c12 = cabs(1, 2)
    if not (c12 > 0):
        return None
    PI3 = iv.pi**3
    up = -4*c12 + 16*cabs(1, 3) + 64*cabs(2, 4)
    for m in range(1, MT+1):
        for n in range(m+2, MT+2):
            if (m, n) in ((1, 3), (2, 4)):
                continue
            p = n-m; q = n+m
            up += (PI3/48)*iv.mpf(p*q*(q*q+p*p))*cabs(m, n)
    # TAIL, computed in intervals: pairs with max index in (MT, MT+EX]
    # summed exactly; remainder beyond MT+EX closed geometrically with a
    # DERIVED ratio. From the termwise-exact I_{n+1}(x) <= x I_n(x)/(2(n+1)),
    # each unit increase of the max index n multiplies every four-Bessel
    # product in |c_mn| by at most (x_hi/(2(n+1)))^4, the coefficient m,n
    # weights by (n+1)/n and pq(q^2+p^2) <= q^4 by ((q+1)/q)^4 <= ((2n+2)/(2n))^4.
    X_hi = iv.mpf(r2[0])/iv.mpf(r2[1])
    n0 = MT + EX + 1
    ratio = (X_hi/(2*iv.mpf(n0+1)))**4             * iv.mpf(n0+1)/iv.mpf(n0) * ((iv.mpf(n0+1))/iv.mpf(n0))**4
    assert ratio < iv.mpf(1)/2, "tail ratio bound failed"
    tail = iv.mpf(0)
    for m in range(1, MT+EX+1):
        for n in range(max(m+2, MT+1), MT+EX+2):
            p = n-m; q = n+m
            tail += (PI3/48)*iv.mpf(p*q*(q*q+p*p))*cabs(m, n)
    up += iv.mpf([0, 1])*tail*(1 + ratio/(1-ratio))
    return up


def cover(x_lo, x_hi, prec=100, verbose=True):
    boxes = []
    stack = [(x_lo, x_hi)]
    D = 10**6
    while stack:
        x1, x2 = stack.pop()
        r1 = (int(x1*D), D)
        r2 = (int(x2*D)+1, D)
        up = crit_box(r1, r2, prec=prec)
        if up is not None and up < 0:
            boxes.append((x1, x2))
            if verbose:
                print("  box [%.4f, %.4f] certified" % (x1, x2), flush=True)
        else:
            if x2 - x1 < 1e-4:
                raise RuntimeError("cannot certify near beta = %.6f" % x1)
            mid = (x1+x2)/2
            stack.append((mid, x2))
            stack.append((x1, mid))
    return boxes


if __name__ == "__main__":
    import sys
    x1 = float(sys.argv[1]) if len(sys.argv) > 1 else 0.05
    x2 = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
    prec = int(sys.argv[3]) if len(sys.argv) > 3 else 100
    boxes = cover(x1, x2, prec, verbose=True)   # per-box progress
    print("pass 1: CERTIFIED Crit < 0 on [%g, %g], %d boxes (prec=%d)"
          % (x1, x2, len(boxes), prec), flush=True)
    # SELF-EXECUTING STABILITY PASS: re-certify every box at prec+70
    D = 10**6
    for (y1, y2) in boxes:
        up = crit_box((int(y1*D), D), (int(y2*D)+1, D), prec=prec+70)
        assert up is not None and up < 0, "STABILITY FAILURE at %.4f" % y1
    print("pass 2: all %d boxes re-certified at prec=%d  (STABLE)"
          % (len(boxes), prec+70))
