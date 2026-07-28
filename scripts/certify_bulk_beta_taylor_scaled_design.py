"""Design probe for an exponentially scaled finite-beta bulk bridge.

This module does not carry theorem load.  It tests the exact replacement

    J_n(beta) = exp(-beta) I_n(beta),

under which both Fourier coefficient families acquire the common factor
``exp(-4 beta)`` and hence the Wronskian ``W`` acquires the strictly positive
factor ``exp(-8 beta)``.  The sign target is therefore unchanged, while the
numbers passed to Arb stay moderate when beta is large.

The production module ``certify_bulk_beta_taylor_arb.py`` is imported but is
never modified on disk.  This design process supplies a scaled Bessel jet
backend to its already audited Taylor algebra.  Promotion requires a separate
source file with a proved derivative-tail contract, provenance, exhaustive
coverage, and an executable validator.
"""

from fractions import Fraction
from math import comb, factorial
import sys

from flint import arb, ctx

import certify_bulk_beta_taylor_arb as bulk


ORIGINAL_BOX_W = bulk.BetaTaylorBox.W


def scaled_bessel_value(n: int, x: Fraction) -> arb:
    """Certified Arb enclosure of exp(-x) I_n(x) at rational x."""
    xx = bulk.aq(x)
    return (-xx).exp()*xx.bessel_i(abs(n))


def scaled_bessel_jet(n: int, x: Fraction, order: int) -> list[arb]:
    """Taylor coefficients J_n^(q)(x)/q!, q=0,...,order.

    The Bessel shift identity is applied before multiplication by the exact
    Taylor series of exp(-h).  Thus no numerical differentiation is used.
    """
    shifted = {
        k: scaled_bessel_value(k, x)
        for k in range(max(0, abs(n)-order), abs(n)+order+1)
    }
    i_taylor = []
    for q in range(order+1):
        derivative = sum(
            (arb(comb(q, j))*shifted[abs(n-q+2*j)]
             for j in range(q+1)), arb(0))/arb(2)**q
        i_taylor.append(derivative/arb(factorial(q)))
    out = []
    for q in range(order+1):
        out.append(sum(
            (i_taylor[j]*arb((-1)**(q-j))/arb(factorial(q-j))
             for j in range(q+1)), arb(0)))
    return out


def scaled_coefficient_jets(m: int, x: Fraction,
                            order: int) -> tuple[list[arb], list[arb]]:
    """Exact beta derivatives of the two scaled coefficient families."""
    jm = scaled_bessel_jet(m, x, order)
    jl = scaled_bessel_jet(m-1, x, order)
    jr = scaled_bessel_jet(m+1, x, order)
    jm2 = bulk.jet_mul(jm, jm, order)
    jl2 = bulk.jet_mul(jl, jl, order)
    jr2 = bulk.jet_mul(jr, jr, order)
    q = [(m-1)*jl2[j]+(m+1)*jr2[j] for j in range(order+1)]
    aj = bulk.jet_mul(jm2, q, order)
    bj = bulk.jet_mul(jm2, jm2, order)
    return ([aj[j]*factorial(j) for j in range(order+1)],
            [arb(m)*bj[j]*factorial(j) for j in range(order+1)])


def scaled_general_derivative_tail(c_k: arb, k: int, r: arb,
                                   beta_lo: Fraction, q: int,
                                   weight_power: int = 0) -> arb:
    """Positive tail majorant for q beta derivatives of scaled coefficients.

    For ``J_n=exp(-beta)I_n``, the exact operator

        J_n'=(J_{n-1}+J_{n+1})/2-J_n

    and ``I_{n-1}/I_n=I_{n+1}/I_n+2n/beta`` give

        |J_n^(p)| <= [2(1+2n/beta)]^p J_n.

    Each coefficient is a positive sum of degree-four monomials in adjacent
    J's.  Leibniz therefore bounds its q-th derivative by
    ``[8(1+2(m+1)/beta)]^q`` times the coefficient.  This is the production
    tail contract with the extra factor two required by exponential scaling;
    reusing the unscaled factor four would be invalid.
    """
    blo = bulk.aq(beta_lo)
    total = arb(0)
    for j in range(10000):
        m = k+j
        factor = 8*(1+2*arb(m+1)/blo)
        term = c_k*r**j*factor**q*arb(m)**weight_power
        total += term
        factor_ratio = ((1+2*arb(m+2)/blo)
                        /(1+2*arb(m+1)/blo))
        ratio = r*factor_ratio**q
        if weight_power:
            ratio *= (arb(m+1)/arb(m))**weight_power
        if ratio < arb(1)/2 and term < arb(10)**(-75):
            return total+term*ratio/(1-ratio)
    raise RuntimeError("scaled derivative-tail majorant did not converge")


def cached_scaled_w(self, t_lo: Fraction, t_hi: Fraction) -> arb:
    """The audited Taylor enclosure with one shared trigonometric cache.

    The production implementation recomputes sin(m*T), cos(m*T) inside each
    beta/t derivative request.  Here those identical Arb balls are formed once
    per mode and t-derivative order.  No approximation or mathematical bound
    changes; an overlap regression compares this method with the original.
    """
    ctx.prec = self.prec
    t_mid = (t_lo+t_hi)/2
    t_rad = (t_hi-t_lo)/2
    T = bulk.aq(t_mid)
    trig_values = [(arb(0), arb(0))]*(self.M+1)
    for m in range(1, self.M+1):
        mt = arb(m)*T
        trig_values[m] = (mt.sin(), mt.cos())
    weighted_trig = []
    for r in range(self.t_order+2):
        row = [arb(0)]*(self.M+1)
        for m in range(1, self.M+1):
            sine, cosine = trig_values[m]
            trig = self.trig_derivative(sine, cosine, r)
            row[m] = arb(m)**r*trig
        weighted_trig.append(row)

    if not hasattr(self, "_scaled_fourier_tails"):
        tails = {}
        for family in ("a", "b"):
            tail_source = self.ac if family == "a" else self.bc
            for q in range(self.order+1):
                for r in range(self.t_order+2):
                    tails[family, q, r] = scaled_general_derivative_tail(
                        tail_source[self.M+1], self.M+1, self.r,
                        self.beta_mid, q, r)
        self._scaled_fourier_tails = tails

    fourier = {}
    for family in ("a", "b"):
        jets = self.aj if family == "a" else self.bj
        tail_source = self.ac if family == "a" else self.bc
        for q in range(self.order+1):
            for r in range(self.t_order+2):
                value = sum((jets[m][q]*weighted_trig[r][m]
                             for m in range(1, self.M+1)), arb(0))
                tail = self._scaled_fourier_tails[family, q, r]
                fourier[family, q, r] = value+bulk.pm1()*tail

    hb = bulk.hull(-bulk.aq(self.beta_rad), bulk.aq(self.beta_rad))
    ht = bulk.hull(-bulk.aq(t_rad), bulk.aq(t_rad))
    out = arb(0)
    hb_power = arb(1)
    for q in range(self.order+1):
        ht_power = arb(1)
        for r in range(self.t_order+1):
            out += (self.mixed_W(fourier, q, r)*hb_power*ht_power
                    /arb(factorial(q)*factorial(r)))
            ht_power *= ht
        hb_power *= hb

    q = self.order+1
    abs_wq = arb(0)
    for j in range(q+1):
        sa, sb, sma, smb = self.abs_sums[j]
        ta, tb, tma, tmb = self.abs_sums[q-j]
        abs_wq += 2*arb(comb(q, j))*(sma*tb+sa*tmb)
    remainder = (bulk.aq(self.beta_rad)**q*abs_wq
                 /arb(factorial(q)))
    rt = self.t_order+1
    t_remainder = arb(0)
    for qb in range(self.order+1):
        t_remainder += (
            bulk.aq(self.beta_rad)**qb/arb(factorial(qb))
            *bulk.aq(t_rad)**rt/arb(factorial(rt))
            *self.abs_mixed_center(qb, rt))
    return out+(remainder+t_remainder)*bulk.pm1()


def install_design_backend() -> None:
    """Install the isolated backend in this process only."""
    bulk.enc_I = scaled_bessel_value
    bulk.bessel_jet = scaled_bessel_jet
    bulk.coefficient_jets = scaled_coefficient_jets
    bulk.general_derivative_tail = scaled_general_derivative_tail
    bulk.BetaTaylorBox.W = cached_scaled_w


def overlap_regression(beta: Fraction = Fraction(20),
                       modes: int = 8, order: int = 4) -> None:
    """Check scaled derivatives against the product-rule transformation.

    If ``a`` is an unscaled degree-four coefficient and ``A=e^-4beta a``,
    then A^(q)=e^-4beta sum_j C(q,j)(-4)^(q-j) a^(j).
    """
    ctx.prec = 180
    scale = (-4*bulk.aq(beta)).exp()
    for m in range(1, modes+1):
        raw_a, raw_b = bulk.coefficient_jets.__wrapped__(m, beta, order) \
            if hasattr(bulk.coefficient_jets, "__wrapped__") else (None, None)
        # The production function is saved explicitly by main before the
        # design backend is installed.  This branch protects direct imports.
        if raw_a is None:
            raise RuntimeError("raw coefficient backend was not registered")
        scaled_a, scaled_b = scaled_coefficient_jets(m, beta, order)
        for q in range(order+1):
            target_a = scale*sum(
                (arb(comb(q, j))*(-4)**(q-j)*raw_a[j]
                 for j in range(q+1)), arb(0))
            target_b = scale*sum(
                (arb(comb(q, j))*(-4)**(q-j)*raw_b[j]
                 for j in range(q+1)), arb(0))
            if not scaled_a[q].overlaps(target_a):
                raise AssertionError(("A", m, q, scaled_a[q], target_a))
            if not scaled_b[q].overlaps(target_b):
                raise AssertionError(("B", m, q, scaled_b[q], target_b))


def main() -> int:
    ctx.prec = 180
    raw_backend = bulk.coefficient_jets
    # Attach a private reference used only by the overlap regression.
    raw_backend.__wrapped__ = raw_backend
    overlap_regression()
    print("SCALED BULK OVERLAP PASS modes=8 derivatives=0..4 beta=20",
          flush=True)
    install_design_backend()
    lo = Fraction(sys.argv[1]) if len(sys.argv) > 1 else Fraction(20)
    hi = Fraction(sys.argv[2]) if len(sys.argv) > 2 else Fraction(201, 10)
    db = Fraction(sys.argv[3]) if len(sys.argv) > 3 else hi-lo
    total = bulk.cover(lo, hi, db=db, prec=180, order=12, t_order=9)
    print("SCALED BULK DESIGN PASS", float(lo), float(hi),
          "t_boxes", total, "NO THEOREM LOAD", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
