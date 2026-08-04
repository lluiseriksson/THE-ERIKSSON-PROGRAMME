"""Arb (python-flint) port of certify_thmB.py - SECOND WITNESS.

Same pinned statement, same exact skeleton, same shell-closed tail:
see the mpmath.iv twin's docstring. Ball arithmetic via python-flint.
Runs the adaptive cover of [1/20, 3] and the full stability pass.
"""
from flint import arb, ctx
from math import factorial

MT = 60
EX = 24


def hull(lo, hi):
    try:
        return lo.union(hi)
    except AttributeError:
        return (lo + hi) / 2 + ((hi - lo) / 2) * arb("0 +/- 1")


def zerone():
    return arb("0.5 +/- 0.5")   # the interval [0, 1]


def enc_I_at(m, num, den):
    """enclosure of I_m(num/den): positive series + geometric tail."""
    X = arb(num) / arb(2 * den)
    s = arb(0)
    j = 0
    while True:
        t = X ** (m + 2 * j) / (arb(factorial(j)) * arb(factorial(m + j)))
        s += t
        if (j + 1) * (m + j + 1) >= 20:   # ratio <= (3/2)^2/20 < 1/2
            if t < arb(10) ** (-60):
                r = (X * X) / (arb(j + 1) * arb(m + j + 1))
                return s + zerone() * (t * r / (1 - r))
        j += 1


def crit_box(r1, r2, prec=100):
    ctx.prec = prec
    I = [hull(enc_I_at(m, *r1), enc_I_at(m, *r2)) for m in range(MT+EX+3)]
    a = [arb(0)] * (MT+EX+2)
    b = [arb(0)] * (MT+EX+2)
    for m in range(1, MT+EX+2):
        a[m] = I[m]**2 * ((m-1)*I[m-1]**2 + (m+1)*I[m+1]**2)
        b[m] = arb(m) * I[m]**4
    def cabs(m, n):
        return a[n]*b[m] - a[m]*b[n]
    c12 = cabs(1, 2)
    if not (c12 > 0):
        return None
    PI3 = arb.pi()**3
    up = -4*c12 + 16*cabs(1, 3) + 64*cabs(2, 4)
    for m in range(1, MT+1):
        for n in range(m+2, MT+2):
            if (m, n) in ((1, 3), (2, 4)):
                continue
            p = n-m; q = n+m
            up += (PI3/48) * arb(p*q*(q*q+p*p)) * cabs(m, n)
    # shell-closed tail (see mpmath twin): per-pair ratio r, shell ratio 2r
    X_hi = arb(r2[0]) / arb(r2[1])
    n0 = MT + EX + 1
    r_pair = (X_hi/(2*arb(n0+1)))**4 * arb(n0+1)/arb(n0) * (arb(n0+1)/arb(n0))**4
    r_shell = 2*r_pair
    assert r_shell < arb(1)/2, "shell ratio bound failed"
    tail = arb(0)
    for m in range(1, MT+EX+1):
        for n in range(max(m+2, MT+1), MT+EX+2):
            p = n-m; q = n+m
            tail += (PI3/48) * arb(p*q*(q*q+p*p)) * cabs(m, n)
    up += zerone() * tail * (1 + r_shell/(1-r_shell))
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
    boxes = cover(x1, x2, prec, verbose=True)
    print("pass 1 (Arb): CERTIFIED Crit < 0 on [%g, %g], %d boxes (prec=%d)"
          % (x1, x2, len(boxes), prec), flush=True)
    D = 10**6
    for (y1, y2) in boxes:
        up = crit_box((int(y1*D), D), (int(y2*D)+1, D), prec=prec+70)
        assert up is not None and up < 0, "STABILITY FAILURE at %.4f" % y1
    print("pass 2 (Arb): all %d boxes re-certified at prec=%d  (STABLE)"
          % (len(boxes), prec+70), flush=True)
