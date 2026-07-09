"""Arb port of certify_bulk.py — the [3.5, 6] bulk machine (seal, box 1).

PINNED STATEMENT (plain mode): W(t, beta) < 0 for all
(t, beta) in [0.6, pi - 1.5/beta] x [covered beta range].
Method, coverage contract, moving pi-boundary and the extended-0-block
assignment of [0.05, 0.6]: see the mpmath.iv twin's docstring.
"""
from flint import arb, ctx
from math import factorial, pi as PI_F

CWIN = 1.5


def hull(lo, hi):
    try:
        return lo.union(hi)
    except AttributeError:
        return (lo + hi)/2 + ((hi - lo)/2)*arb("0 +/- 1")


def pm1():
    return arb("0 +/- 1")


def enc_I_at(m, num, den):
    X = arb(num)/arb(2*den)
    s = arb(0)
    j = 0
    while True:
        t = X**(m+2*j)/(arb(factorial(j))*arb(factorial(m+j)))
        s += t
        if (j+1)*(m+j+1) >= 82:
            if t < arb(10)**(-60):
                r = (X*X)/(arb(j+1)*arb(m+j+1))
                return s + hull(arb(0), t*r/(1-r))
        j += 1


class BetaBox:
    def __init__(self, r1, r2, prec=110):
        ctx.prec = prec
        self.prec = prec
        bhi = r2[0]/r2[1]
        self.M = int(bhi) + 50
        M = self.M
        I = [hull(enc_I_at(m, *r1), enc_I_at(m, *r2)) for m in range(M+3)]
        self.a = [arb(0)]*(M+2)
        self.b = [arb(0)]*(M+2)
        for m in range(1, M+2):
            self.a[m] = I[m]**2*((m-1)*I[m-1]**2 + (m+1)*I[m+1]**2)
            self.b[m] = arb(m)*I[m]**4
        X_hi = arb(r2[0])/arb(r2[1])
        r = (X_hi/(2*arb(M)))**4 * (arb(M+1)/arb(M))**2
        assert r < arb(1)/2, "coefficient tail ratio failed"
        gA = self.a[M+1]/(1-r)
        gB = self.b[M+1]/(1-r)
        gAw = 2*arb(M+1)*self.a[M+1]/(1-r)**2
        gBw = 2*arb(M+1)*self.b[M+1]/(1-r)**2
        self.tails = (gA, gB, gAw, gBw)

    def G(self, t1q, t2q, margin=False):
        ctx.prec = self.prec
        T = hull(arb(t1q[0])/arb(t1q[1]), arb(t2q[0])/arb(t2q[1]))
        M = self.M
        FA = arb(0); FB = arb(0); FAp = arb(0); FBp = arb(0)
        for m in range(1, M+1):
            sm = (arb(m)*T).sin(); cm = (arb(m)*T).cos()
            FA += self.a[m]*sm
            FB += self.b[m]*sm
            FAp += arb(m)*self.a[m]*cm
            FBp += arb(m)*self.b[m]*cm
        gA, gB, gAw, gBw = self.tails
        FA += pm1()*gA; FB += pm1()*gB; FAp += pm1()*gAw; FBp += pm1()*gBw
        W = 2*(FAp*FB - FA*FBp)
        if margin:
            W = W + (T/2).sin()*FB**2
        return W


def cover_t(bb, t_lo, t_hi, margin=False):
    D = 10**6
    count = 0
    stack = [(t_lo, t_hi)]
    while stack:
        x1, x2 = stack.pop()
        G = bb.G((int(x1*D), D), (int(x2*D)+1, D), margin=margin)
        if G < 0:
            count += 1
        else:
            if x2 - x1 < 5e-5:
                raise RuntimeError("bulk failure near t=%.5f" % x1)
            mid = (x1+x2)/2
            stack.append((mid, x2)); stack.append((x1, mid))
    return count


def cover(b_lo, b_hi, db, t_lo=0.6, margin=False, prec=110):
    D = 10**6
    total = 0
    b = b_lo
    while b < b_hi - 1e-12:
        b2 = min(b + db, b_hi)
        try:
            bb = BetaBox((int(b*D), D), (int(b2*D)+1, D), prec=prec)
            th = PI_F - CWIN/b
            n = cover_t(bb, t_lo, th, margin=margin)
            total += n
            print("beta-box [%.4f, %.4f]: %d t-boxes" % (b, b2, n), flush=True)
            b = b2
        except RuntimeError as e:
            if db < 5e-5:
                raise
            db = db/2
            print("  narrowing beta step to %.6f at beta=%.4f (%s)"
                  % (db, b, e), flush=True)
    return total


if __name__ == "__main__":
    import sys
    b1 = float(sys.argv[1]); b2 = float(sys.argv[2])
    db = float(sys.argv[3]) if len(sys.argv) > 3 else 4e-4
    total = cover(b1, b2, db)
    print("CERTIFIED (plain, Arb): W < 0 on [0.6, pi-1.5/beta] x [%g, %g]; %d t-boxes total"
          % (b1, b2, total), flush=True)
