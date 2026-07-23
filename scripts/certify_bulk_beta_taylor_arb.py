"""Rigorous beta-centred Arb certificate for the compact bulk strip.

Target
------
    W(t,beta) < 0,
    0.6 <= t <= pi - 1.5/beta,  3 <= beta <= 15.

The historical ``certify_bulk_arb.py`` encloses every Bessel coefficient
independently over a beta box.  Above beta about 9 this destroys the common
beta correlation.  Here the value is evaluated at the exact rational centre
of the beta box and the mean-value theorem is applied with a rigorous
enclosure of dW/dbeta over the whole box.

All Bessel tails are positive.  If k=M+1 and c_{k+j} <= c_k r^j, the beta
derivative uses

    0 < I_n'(x)/I_n(x) = I_{n+1}(x)/I_n(x) + n/x <= 1+n/x,

and hence c_m' <= 4(1+(m+1)/beta_lo)c_m for both coefficient families.
The zeroth, first and second geometric moments below then enclose the two
derivative tails needed by W.  This file is a new certificate lane; it does
not alter the archived [3,6] transcript.
"""

from fractions import Fraction
import hashlib
from math import comb, factorial
from pathlib import Path
import platform
import subprocess
import sys

import flint
from flint import arb, ctx


CWIN = Fraction(3, 2)
PI_UP = Fraction(31415927, 10_000_000)
D = 10**6


def hull(lo, hi):
    return (lo + hi) / 2 + ((hi - lo) / 2) * arb("0 +/- 1")


def pm1():
    return arb("0 +/- 1")


def aq(q):
    """Exact Arb conversion of a Fraction."""
    return arb(q.numerator) / arb(q.denominator)


def enc_I(m, x):
    """Positive power-series enclosure of I_m(x), x a Fraction."""
    X = aq(x) / 2
    s = arb(0)
    j = 0
    while True:
        term = X ** (m + 2*j) / (arb(factorial(j))*arb(factorial(m+j)))
        s += term
        ratio = X*X / (arb(j+1)*arb(m+j+1))
        if ratio < arb(1)/2 and term < arb(10)**(-70):
            return s + hull(arb(0), term*ratio/(1-ratio))
        j += 1


def coefficient_arrays(I, M):
    a = [arb(0)]*(M+2)
    b = [arb(0)]*(M+2)
    da = [arb(0)]*(M+2)
    db = [arb(0)]*(M+2)
    Ip = [(I[1] if m == 0 else (I[m-1]+I[m+1])/2)
          for m in range(M+3)]
    for m in range(1, M+2):
        q = (m-1)*I[m-1]**2 + (m+1)*I[m+1]**2
        qp = (2*(m-1)*I[m-1]*Ip[m-1]
              + 2*(m+1)*I[m+1]*Ip[m+1])
        a[m] = I[m]**2*q
        b[m] = arb(m)*I[m]**4
        da[m] = 2*I[m]*Ip[m]*q + I[m]**2*qp
        db[m] = 4*arb(m)*I[m]**3*Ip[m]
    return a, b, da, db


def jet_mul(x, y, order):
    return [sum((x[j]*y[q-j] for j in range(q+1)), arb(0))
            for q in range(order+1)]


def bessel_jet(n, x, order):
    """Taylor coefficients I_n^(q)(x)/q!, using the shift identity."""
    out = []
    for q in range(order+1):
        d = sum((arb(comb(q, j))*enc_I(abs(n-q+2*j), x)
                 for j in range(q+1)), arb(0))/arb(2)**q
        out.append(d/arb(factorial(q)))
    return out


def coefficient_jets(m, x, order):
    im = bessel_jet(m, x, order)
    il = bessel_jet(m-1, x, order)
    ir = bessel_jet(m+1, x, order)
    im2 = jet_mul(im, im, order)
    il2 = jet_mul(il, il, order)
    ir2 = jet_mul(ir, ir, order)
    q = [(m-1)*il2[j]+(m+1)*ir2[j] for j in range(order+1)]
    aj = jet_mul(im2, q, order)
    bj = jet_mul(im2, im2, order)
    return ([aj[j]*factorial(j) for j in range(order+1)],
            [arb(m)*bj[j]*factorial(j) for j in range(order+1)])


def value_tails(a, b, M, r):
    k = M+1
    return (a[k]/(1-r), b[k]/(1-r),
            2*arb(k)*a[k]/(1-r)**2,
            2*arb(k)*b[k]/(1-r)**2)


def coefficient_tail_ratio(x, k):
    """Uniform ratio majorant for both coefficient tails from index k.

    The elementary series ratio gives I_{n+1}(x)/I_n(x) <
    x/(2(n+1)).  Applying it to b_m directly and to the two positive
    summands of a_m gives the two expressions below at m=k.  Every factor
    is decreasing for m>=k (here k>=56 and x<=15), so their maximum is a
    common geometric ratio for all subsequent terms.
    """
    m = arb(k)
    q_m = x/(2*(m+1))
    q_prev = x/(2*m)
    rb = (m+1)/m*q_m**4
    ra = q_m**2*q_prev**2*(m+(m+2)*q_m**2)/(m-1)
    return ra if ra > rb else rb


def derivative_tail(c_k, k, r, beta_lo):
    """Return bounds for sum c_m' and sum m*c_m', m>=k."""
    S0 = 1/(1-r)
    S1 = r/(1-r)**2
    S2 = r*(1+r)/(1-r)**3
    blo = aq(beta_lo)
    unweighted = 4*c_k*(S0 + ((k+1)*S0+S1)/blo)
    weighted = 4*c_k*((k*S0+S1)
                      + (k*(k+1)*S0+(2*k+1)*S1+S2)/blo)
    return unweighted, weighted


def general_derivative_tail(c_k, k, r, beta_lo, q, weight_power=0):
    """Positive majorant for sum m^weight_power c_m^(q), m>=k.

    Each coefficient is a sum of degree-four positive Bessel monomials.
    The Bessel shift identity, I_{n+1}/I_n < 1 and the recurrence
    I_{n-1}/I_n=I_{n+1}/I_n+2n/x give the deliberately generous factor
    [4(1+2(m+1)/beta_lo)]^q.  The coefficient tail is
    bounded by c_k*r^(m-k).  The displayed term ratio decreases in m;
    once it is below 1/2 the remaining geometric tail is enclosed.
    """
    blo = aq(beta_lo)
    total = arb(0)
    term = None
    for j in range(10000):
        m = k+j
        L = 4*(1+2*arb(m+1)/blo)
        term = c_k*r**j*L**q*arb(m)**weight_power
        total += term
        Lratio = (1+2*arb(m+2)/blo)/(1+2*arb(m+1)/blo)
        ratio = r*Lratio**q
        if weight_power:
            ratio *= (arb(m+1)/arb(m))**weight_power
        if ratio < arb(1)/2 and term < arb(10)**(-75):
            return total + term*ratio/(1-ratio)
    raise RuntimeError("derivative-tail majorant did not converge")


class BetaTaylorBox:
    def __init__(self, beta_lo, beta_hi, prec=130, order=12, t_order=9):
        if not beta_lo < beta_hi:
            raise ValueError("non-positive beta box")
        ctx.prec = prec
        self.prec = prec
        self.beta_lo = beta_lo
        self.beta_hi = beta_hi
        self.beta_mid = (beta_lo+beta_hi)/2
        self.beta_rad = (beta_hi-beta_lo)/2
        self.order = order
        self.t_order = t_order
        self.M = int(beta_hi)+55
        M = self.M

        self.aj = [[arb(0)]*(order+1) for _ in range(M+2)]
        self.bj = [[arb(0)]*(order+1) for _ in range(M+2)]
        for m in range(1, M+2):
            self.aj[m], self.bj[m] = coefficient_jets(
                m, self.beta_mid, order)

        Ic = [enc_I(m, self.beta_mid) for m in range(M+4)]
        self.ac, self.bc, _, _ = coefficient_arrays(Ic, M)

        xhi = aq(beta_hi)
        r = coefficient_tail_ratio(xhi, M+1)
        if not r < arb(1)/2:
            raise RuntimeError("coefficient-tail ratio is not below 1/2")
        self.r = r
        self.center_tails_by_order = []
        k = M+1
        for q in range(order+1):
            self.center_tails_by_order.append((
                general_derivative_tail(self.ac[k], k, r, self.beta_mid,
                                        q, 0),
                general_derivative_tail(self.bc[k], k, r, self.beta_mid,
                                        q, 0),
                general_derivative_tail(self.ac[k], k, r, self.beta_mid,
                                        q, 1),
                general_derivative_tail(self.bc[k], k, r, self.beta_mid,
                                        q, 1)))

        max_power = t_order+2
        self.abs_center = []
        for q in range(order+1):
            row = []
            for power in range(max_power+1):
                Sa = sum((arb(m)**power*self.aj[m][q]
                          for m in range(1, M+1)), arb(0))
                Sb = sum((arb(m)**power*self.bj[m][q]
                          for m in range(1, M+1)), arb(0))
                Sa += general_derivative_tail(
                    self.ac[k], k, r, self.beta_mid, q, power)
                Sb += general_derivative_tail(
                    self.bc[k], k, r, self.beta_mid, q, power)
                row.append((Sa, Sb))
            self.abs_center.append(row)

        # Absolute derivative sums at beta_hi for the Taylor remainder.
        rem = order+1
        ahi = [arb(0)]*(M+2); bhi = [arb(0)]*(M+2)
        self.abs_sums = []
        jets_hi = [None]*(M+2)
        for m in range(1, M+2):
            jets_hi[m] = coefficient_jets(m, beta_hi, rem)
            ahi[m] = jets_hi[m][0][0]; bhi[m] = jets_hi[m][1][0]
        xhi = aq(beta_hi)
        rr = coefficient_tail_ratio(xhi, M+1)
        for q in range(rem+1):
            Sa = sum((jets_hi[m][0][q] for m in range(1, M+1)), arb(0))
            Sb = sum((jets_hi[m][1][q] for m in range(1, M+1)), arb(0))
            Sma = sum((arb(m)*jets_hi[m][0][q]
                       for m in range(1, M+1)), arb(0))
            Smb = sum((arb(m)*jets_hi[m][1][q]
                       for m in range(1, M+1)), arb(0))
            Sa += general_derivative_tail(ahi[k], k, rr, beta_lo, q, 0)
            Sb += general_derivative_tail(bhi[k], k, rr, beta_lo, q, 0)
            Sma += general_derivative_tail(ahi[k], k, rr, beta_lo, q, 1)
            Smb += general_derivative_tail(bhi[k], k, rr, beta_lo, q, 1)
            self.abs_sums.append((Sa, Sb, Sma, Smb))

    @staticmethod
    def trig_derivative(s, c, r):
        z = r % 4
        return (s, c, -s, -c)[z]

    def fourier_derivative(self, T, q, r, family):
        out = arb(0)
        jets = self.aj if family == "a" else self.bj
        for m in range(1, self.M+1):
            mt = arb(m)*T
            trig = self.trig_derivative(mt.sin(), mt.cos(), r)
            out += arb(m)**r*jets[m][q]*trig
        tail = general_derivative_tail(
            self.ac[self.M+1] if family == "a" else self.bc[self.M+1],
            self.M+1, self.r, self.beta_mid, q, r)
        return out+pm1()*tail

    def mixed_W(self, fourier, q, r):
        out = arb(0)
        for j in range(q+1):
            for ell in range(r+1):
                factor = arb(comb(q, j)*comb(r, ell))
                out += factor*(
                    fourier["a", j, ell+1]*fourier["b", q-j, r-ell]
                    - fourier["a", j, ell]*fourier["b", q-j, r-ell+1])
        return 2*out

    def abs_mixed_center(self, q, r):
        out = arb(0)
        for j in range(q+1):
            for ell in range(r+1):
                Aj, Bj = self.abs_center[j][ell]
                Atj, _ = self.abs_center[j][ell+1]
                Ak, Bk = self.abs_center[q-j][r-ell]
                _, Btk = self.abs_center[q-j][r-ell+1]
                out += arb(comb(q, j)*comb(r, ell))*(Atj*Bk+Aj*Btk)
        return 2*out

    def W(self, t_lo, t_hi):
        ctx.prec = self.prec
        t_mid = (t_lo+t_hi)/2
        t_rad = (t_hi-t_lo)/2
        T = aq(t_mid)
        fourier = {}
        for family in ("a", "b"):
            for q in range(self.order+1):
                for r in range(self.t_order+2):
                    fourier[family, q, r] = self.fourier_derivative(
                        T, q, r, family)
        Hb = hull(-aq(self.beta_rad), aq(self.beta_rad))
        Ht = hull(-aq(t_rad), aq(t_rad))
        out = arb(0)
        Hbpow = arb(1)
        for q in range(self.order+1):
            Htpow = arb(1)
            for r in range(self.t_order+1):
                out += (self.mixed_W(fourier, q, r)*Hbpow*Htpow
                        /arb(factorial(q)*factorial(r)))
                Htpow *= Ht
            Hbpow *= Hb

        q = self.order+1
        absWq = arb(0)
        for j in range(q+1):
            Sa, Sb, Sma, Smb = self.abs_sums[j]
            Ta, Tb, Tma, Tmb = self.abs_sums[q-j]
            absWq += 2*arb(comb(q, j))*(Sma*Tb+Sa*Tmb)
        remainder = aq(self.beta_rad)**q*absWq/arb(factorial(q))
        # Taylor remainder in t for each retained beta derivative.
        rt = self.t_order+1
        t_remainder = arb(0)
        for qb in range(self.order+1):
            t_remainder += (aq(self.beta_rad)**qb/arb(factorial(qb))
                            * aq(t_rad)**rt/arb(factorial(rt))
                            * self.abs_mixed_center(qb, rt))
        return out + (remainder+t_remainder)*pm1()


def cover_t(bb, t_lo, t_hi, min_dt=Fraction(1, 100_000)):
    count = 0
    stack = [(t_lo, t_hi)]
    while stack:
        x1, x2 = stack.pop()
        W = bb.W(x1, x2)
        if W < 0:
            count += 1
        elif x2-x1 <= min_dt:
            raise RuntimeError("bulk failure near t=%s" % float(x1))
        else:
            mid = (x1+x2)/2
            stack.append((mid, x2)); stack.append((x1, mid))
    return count


def cover(beta_lo, beta_hi, db=Fraction(1, 10), prec=130,
          order=12, t_order=9):
    total = 0
    b = beta_lo
    step = db
    while b < beta_hi:
        b2 = min(b+step, beta_hi)
        try:
            bb = BetaTaylorBox(b, b2, prec=prec, order=order,
                               t_order=t_order)
            # The moving upper boundary is increasing in beta.  PI_UP is a
            # strict rational upper bound for pi, so this covers a superset.
            t_hi = PI_UP-CWIN/b2
            n = cover_t(bb, Fraction(3, 5), t_hi)
            print("beta-box [%s, %s]: %d t-boxes" %
                  (float(b), float(b2), n), flush=True)
            total += n
            b = b2
        except RuntimeError as exc:
            if step <= Fraction(1, 1_000_000):
                raise
            step /= 2
            print("narrowing beta step to %s at beta=%s (%s)" %
                  (float(step), float(b), exc), flush=True)
    return total


def fq(s):
    return Fraction(s)


def provenance():
    path = Path(__file__).resolve()
    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=path.parents[1], text=True,
            stderr=subprocess.DEVNULL).strip()
    except Exception:
        head = "UNAVAILABLE"
    return {
        "script": str(path.relative_to(path.parents[1])).replace("\\", "/"),
        "script_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "git_head": head,
        "python": platform.python_version(),
        "python_flint": getattr(flint, "__version__", "UNKNOWN"),
        "arb_prec_bits": ctx.prec,
    }


if __name__ == "__main__":
    b1 = fq(sys.argv[1]); b2 = fq(sys.argv[2])
    db = fq(sys.argv[3]) if len(sys.argv) > 3 else Fraction(1, 10)
    order = int(sys.argv[4]) if len(sys.argv) > 4 else 12
    t_order = int(sys.argv[5]) if len(sys.argv) > 5 else 9
    ctx.prec = 130
    for key, value in provenance().items():
        print("PROVENANCE %s=%s" % (key, value), flush=True)
    print("CONFIG prec=130 beta_order=%d t_order=%d initial_db=%s "
          "CWIN=3/2 PI_UP=31415927/10000000" %
          (order, t_order, float(db)), flush=True)
    total = cover(b1, b2, db, order=order, t_order=t_order)
    print("CERTIFIED (beta-Taylor, Arb): W < 0 on "
          "[0.6, pi-1.5/beta] x [%s, %s]; %d t-boxes total" %
          (float(b1), float(b2), total), flush=True)
