"""Polynomial-Gaussian derivative tails for the endpoint ball series.

Every normalized delta derivative is majorized by C*rho^p times the
common Gaussian.  The algebra below propagates such majorants and then
integrates them radially outside rho=30.  This is independent of the
finite spatial quadrature.
"""

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import factorial

from flint import arb, arb_series, ctx

from surface_bessel_integral_remainder import (
    aq, relative_coefficients, upper_gamma_elementary,
)
from surface_remainder_delta0_series_design import sinc2_derivatives
from surface_remainder_delta0_series_design import nominal_moment_series, PREC
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_arb_jet2 import hull


ORDER = 5


@dataclass(frozen=True)
class Term:
    c: arb
    p: int


def zero() -> Term:
    return Term(arb(0), 0)


def add_term(a: Term, b: Term) -> Term:
    # rho>=1, so either monomial is bounded by the larger power.
    return Term(a.c+b.c, max(a.p, b.p))


def mul_term(a: Term, b: Term) -> Term:
    return Term(a.c*b.c, a.p+b.p)


def scale_term(a: Term, value: arb) -> Term:
    return Term(a.c*arb(value.abs_upper()), a.p)


def const(value) -> list[Term]:
    return [Term(arb(abs(value)), 0)]+[zero() for _ in range(ORDER)]


def add(a, b):
    return [add_term(x, y) for x, y in zip(a, b)]


def mul(a, b):
    out = [zero() for _ in range(ORDER+1)]
    for n in range(ORDER+1):
        for k in range(n+1):
            out[n] = add_term(out[n], mul_term(a[k], b[n-k]))
    return out


def scale(a, value):
    return [scale_term(x, arb(value)) for x in a]


def inv(a, constant_lower: arb):
    if not constant_lower > 0:
        raise ValueError("inverse majorant needs a positive constant floor")
    out = [zero() for _ in range(ORDER+1)]
    out[0] = Term(1/constant_lower, 0)
    for n in range(1, ORDER+1):
        total = zero()
        for k in range(1, n+1):
            total = add_term(total, mul_term(a[k], out[n-k]))
        out[n] = scale_term(total, 1/constant_lower)
    return out


def sqrt_series(a, root_lower: arb):
    out = [zero() for _ in range(ORDER+1)]
    out[0] = Term(arb(1), 0)  # sqrt(a0)<=1 in the present geometry
    for n in range(1, ORDER+1):
        total = a[n]
        for k in range(1, n):
            total = add_term(total, mul_term(out[k], out[n-k]))
        out[n] = scale_term(total, 1/(2*root_lower))
    return out


def exp_relative(phase):
    """Bounds exp(phase)/exp(phase_0), coefficient by coefficient."""
    out = [zero() for _ in range(ORDER+1)]
    out[0] = Term(arb(1), 0)
    for n in range(1, ORDER+1):
        total = zero()
        for k in range(1, n+1):
            total = add_term(
                total, scale_term(mul_term(phase[k], out[n-k]), arb(k)))
        out[n] = scale_term(total, arb(1)/n)
    return out


def polynomial(series, coefficients):
    out = const(0)
    for coefficient in reversed(coefficients):
        out = add(mul(out, series), const(aq(abs(coefficient))))
    return out


def moment_majorants():
    cmin = arb(2).sqrt()/2
    u = arb("0.6").sin()**2
    root_lower = (1-2*u).sqrt()
    d = [Term(arb("0.001"), 0), Term(arb(1), 0)] \
        +[zero() for _ in range(ORDER-1)]
    y = hull(arb(0), arb("0.36"))
    derivatives = sinc2_derivatives(y, ORDER)
    p = [Term(arb(derivatives[k].abs_upper())
              /arb(factorial(k)*4**(k+1)), 2*k+2)
         for k in range(ORDER+1)]
    q = list(p)
    pq = mul(p, q)
    w = add(add(p, q), scale(mul(d, pq), arb(2)))
    radicand = add(const(1), scale(mul(d, w), arb(1)))
    root = sqrt_series(radicand, root_lower)
    root_inv = inv(root, root_lower)
    one_plus_root_inv = inv(add(const(1), root), 1+root_lower)
    phase = scale(mul(w, one_plus_root_inv), arb(4))
    exponential = exp_relative(phase)
    h = scale(mul(d, root_inv), 1/(4*cmin))
    a_poly = polynomial(h, relative_coefficients("A", 4))
    b_poly = polynomial(h, relative_coefficients("B", 4))
    root_half_inv = inv(sqrt_series(root, root_lower.sqrt()),
                        root_lower.sqrt())
    root_3half_inv = mul(root_inv, root_half_inv)
    root_5half_inv = mul(mul(root_inv, root_inv), root_half_inv)
    psum = add(p, q)
    d_weight = scale(add(const(1), mul(d, psum)), arb(2))
    # Absolute version of the exact F/delta bracket, with |cc|<=1.
    bracket = add(const(3), add(
        scale(mul(d, p), arb(3)),
        add(scale(mul(d, q), arb(3)),
            scale(mul(mul(d, d), pq), arb(2)))))
    f_over = scale(mul(p, bracket), arb(4))
    common = 1/(2*arb.pi()).sqrt()
    kernel = scale(mul(root_3half_inv, a_poly),
                   2*common/(4*cmin)**(arb(3)/2))
    hregular = scale(mul(root_5half_inv, b_poly),
                     common/(4*cmin)**(arb(5)/2))
    return {
        "kd": mul(mul(kernel, d_weight), exponential),
        "kf": mul(mul(kernel, f_over), exponential),
        "hdd": mul(mul(hregular, mul(d_weight, d_weight)), exponential),
        "hdf": mul(mul(hregular, mul(d_weight, f_over)), exponential),
    }


def gaussian_rate() -> arb:
    cmin = arb(2).sqrt()/2
    u = arb("0.6").sin()**2
    sinc = arb("0.6").sin()/arb("0.6")
    return 2*cmin*(1-u)*sinc**2/4


def radial_tail(term: Term, radius: int = 30) -> arb:
    """Four-quadrant integral outside the square [0,radius]^2."""
    rate = gaussian_rate()
    s = Fraction(term.p+2, 2)
    z = rate*radius**2
    gamma = upper_gamma_elementary(s, z)
    radial = gamma/(2*rate**aq(s))
    return 2*arb.pi()*term.c*radial


def derivative_tail_bounds(radius: int = 32):
    majorants = moment_majorants()
    return {name: [radial_tail(term, radius) for term in series]
            for name, series in majorants.items()}


@lru_cache(maxsize=None)
def annulus_derivative_bounds(inner: int = 12, outer: int = 32,
                              width=Fraction(1, 2)):
    """Absolute derivatives on the uniform t annulus.

    A cell is differentiated only up to the delta for which its scaled
    physical coordinates are at most 1.  The remaining physical band
    1<max(s,alpha)<=1.2 is exponentially flat and charged separately.
    Every cell contribution is symmetrized, so zero (cell absent from a
    smaller moving domain) is also enclosed.
    """
    w = aq(width)
    lo, hi = int(Fraction(inner)/width), int(Fraction(outer)/width)
    dmax, physical_inner = arb("0.001"), arb(1)
    t = hull(arb(0), arb.pi())
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("kd", "kf", "hdd", "hdf")}
    for i in range(hi):
        for j in range(hi):
            if i < lo and j < lo:
                continue
            shi, ahi = w*(i+1), w*(j+1)
            cap = min(dmax, (physical_inner/shi)**2,
                      (physical_inner/ahi)**2)
            values = nominal_moment_series(
                hull(arb(0), cap), t,
                hull(w*i, shi), hull(w*j, ahi))
            area = 4*w**2
            for name, series in values.items():
                for order, value in enumerate(series.coeffs()):
                    totals[name][order] += area*arb(value.abs_upper())
    return totals


def moving_band_value_coefficients(delta_max=arb("0.001")):
    """e_M with the moving physical band bounded by e_M*delta^5."""
    majorants = moment_majorants()
    # The band begins when max(s,alpha)=1, hence rho>=1/sqrt(delta).
    # After division by delta^5, the elementary gamma majorant is largest
    # at delta_max: rate/delta_max exceeds s+5 for every stored power.
    threshold = gaussian_rate()/delta_max
    out = {}
    radius_lower = 31  # 31 < 1/sqrt(0.001); outward-safe weakening
    for name, series in majorants.items():
        assert all(threshold > aq(Fraction(term.p+2, 2)+5)
                   for term in series[:5])
        missing_coefficients = sum((
            radial_tail(term, radius_lower)*delta_max**(order-5)
            for order, term in enumerate(series[:5])
        ), arb(0))
        # Taylor's integral remainder in the physical band itself.
        remainder = radial_tail(series[5], radius_lower)
        out[name] = missing_coefficients+remainder
    return out


@lru_cache(maxsize=1)
def outer_derivative_bounds():
    annulus = annulus_derivative_bounds()
    tail = derivative_tail_bounds(32)
    return {name: [annulus[name][k]+tail[name][k]
                   for k in range(PREC)] for name in annulus}


def add_outer_derivatives(series: dict[str, arb_series]):
    outer = outer_derivative_bounds()
    result = {}
    for name, value in series.items():
        coefficients = value.coeffs()+[arb(0)]*PREC
        result[name] = arb_series([
            coefficients[k]+outer[name][k]*arb("0 +/- 1")
            for k in range(PREC)
        ], PREC)
    return result


def check() -> None:
    ctx.prec = 180
    tails = derivative_tail_bounds(32)
    assert all(value.is_finite() and value > 0
               for row in tails.values() for value in row)
    for name, row in tails.items():
        print(name, [value.str(8) for value in row])
    bands = moving_band_value_coefficients()
    print("moving-band delta^5 coefficients",
          {name: value.str(8) for name, value in bands.items()})
    # The separate companion error is value-only and is not hidden here.
    assert moment_error_coefficients().hdf > 0
    print("DELTA0 OUTER NORMALIZED DERIVATIVE TAILS BOUNDED")


if __name__ == "__main__":
    check()
