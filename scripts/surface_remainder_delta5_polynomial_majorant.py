"""Degree-preserving polynomial-Gaussian majorant for the delta^5 tail.

This design engine keeps every spatial degree separate until Gaussian
integration.  It avoids the rejected monomial collapse that promoted all
terms to degree 68.  The output bounds moment derivatives, not yet the
head-subtracted quotient remainder.
"""

from fractions import Fraction
from math import factorial

from flint import arb, ctx

from surface_bessel_integral_remainder import aq, relative_coefficients
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_series_design import sinc2_derivatives


ORDER = 6
Poly = dict[int, arb]


def pb(terms=None) -> Poly:
    out = {}
    for power, coefficient in (terms or {}).items():
        if coefficient != 0:
            out[power] = arb(coefficient)
    return out


def padd(a: Poly, b: Poly) -> Poly:
    out = dict(a)
    for power, coefficient in b.items():
        out[power] = out.get(power, arb(0))+coefficient
    return pb(out)


def pmul(a: Poly, b: Poly) -> Poly:
    out = {}
    for pa, ca in a.items():
        for pb_, cb in b.items():
            power = pa+pb_
            out[power] = out.get(power, arb(0))+ca*cb
    return pb(out)


def pscale(a: Poly, value) -> Poly:
    magnitude = arb(arb(value).abs_upper())
    return pb({power: coefficient*magnitude
               for power, coefficient in a.items()})


def zero_series():
    return [pb() for _ in range(ORDER+1)]


def constant(value):
    return [pb({0: arb(abs(value))})]+[pb() for _ in range(ORDER)]


def sadd(a, b):
    return [padd(x, y) for x, y in zip(a, b)]


def sscale(a, value):
    return [pscale(x, value) for x in a]


def smul(a, b):
    out = zero_series()
    for n in range(ORDER+1):
        for k in range(n+1):
            out[n] = padd(out[n], pmul(a[k], b[n-k]))
    return out


def sinv(a, constant_lower):
    floor = arb(constant_lower)
    out = zero_series()
    out[0] = pb({0: 1/floor})
    for n in range(1, ORDER+1):
        total = pb()
        for k in range(1, n+1):
            total = padd(total, pmul(a[k], out[n-k]))
        out[n] = pscale(total, 1/floor)
    return out


def ssqrt(a, root_lower):
    floor = arb(root_lower)
    out = zero_series()
    out[0] = pb({0: arb(1)})
    for n in range(1, ORDER+1):
        total = dict(a[n])
        for k in range(1, n):
            total = padd(total, pmul(out[k], out[n-k]))
        out[n] = pscale(total, 1/(2*floor))
    return out


def sexp_relative(phase):
    out = zero_series()
    out[0] = pb({0: arb(1)})
    for n in range(1, ORDER+1):
        total = pb()
        for k in range(1, n+1):
            total = padd(total, pscale(
                pmul(phase[k], out[n-k]), arb(k)))
        out[n] = pscale(total, arb(1)/n)
    return out


def spoly(series, coefficients):
    out = constant(0)
    for coefficient in reversed(coefficients):
        out = sadd(smul(out, series), constant(aq(abs(coefficient))))
    return out


def moment_polynomial_majorants(delta_max=arb("0.05")):
    cmin = arb(2).sqrt()/2
    u = arb("0.6").sin()**2
    root_floor = (1-2*u).sqrt()
    d = [pb({0: delta_max}), pb({0: arb(1)})] \
        +[pb() for _ in range(ORDER-1)]
    derivatives = sinc2_derivatives(hull(arb(0), arb("0.36")), ORDER)
    p = [pb({2*k+2: arb(derivatives[k].abs_upper())
                    /arb(factorial(k)*4**(k+1))})
         for k in range(ORDER+1)]
    q = list(p)
    pq = smul(p, q)
    w = sadd(sadd(p, q), sscale(smul(d, pq), arb(2)))
    radicand = sadd(constant(1), smul(d, w))
    root = ssqrt(radicand, root_floor)
    root_inv = sinv(root, root_floor)
    one_plus_inv = sinv(sadd(constant(1), root), 1+root_floor)
    phase = sscale(smul(w, one_plus_inv), arb(4))
    exponential = sexp_relative(phase)
    h = sscale(smul(d, root_inv), 1/(4*cmin))
    arel = spoly(h, relative_coefficients("A", 5))
    brel = spoly(h, relative_coefficients("B", 5))
    root_half_inv = sinv(ssqrt(root, root_floor.sqrt()), root_floor.sqrt())
    root3 = smul(root_inv, root_half_inv)
    root5 = smul(smul(root_inv, root_inv), root_half_inv)
    dweight = sscale(sadd(constant(1), smul(d, sadd(p, q))), arb(2))
    bracket = sadd(constant(3), sadd(
        sscale(smul(d, p), arb(3)), sadd(
            sscale(smul(d, q), arb(3)),
            sscale(smul(smul(d, d), pq), arb(2)))))
    f_over = sscale(smul(p, bracket), arb(4))
    common = 1/(2*arb.pi()).sqrt()
    kernel = sscale(smul(root3, arel),
                    2*common/(4*cmin)**(arb(3)/2))
    hkernel = sscale(smul(root5, brel),
                     common/(4*cmin)**(arb(5)/2))
    return {
        "kd": smul(smul(kernel, dweight), exponential),
        "kf": smul(smul(kernel, f_over), exponential),
        "hdd": smul(smul(hkernel, smul(dweight, dweight)), exponential),
        "hdf": smul(smul(hkernel, smul(dweight, f_over)), exponential),
    }


def gaussian_rate():
    cmin = arb(2).sqrt()/2
    u = arb("0.6").sin()**2
    sinc = arb("0.6").sin()/arb("0.6")
    return 2*cmin*(1-u)*sinc**2/4


def integrate_polynomial(poly: Poly):
    """Four-quadrant full-plane radial Gaussian integral."""
    rate = gaussian_rate()
    total = arb(0)
    for power, coefficient in poly.items():
        shape = arb(power+2)/2
        radial = shape.gamma()/(2*rate**shape)
        total += 2*arb.pi()*coefficient*radial
    return total


def sixth_moment_bounds():
    majorants = moment_polynomial_majorants()
    return {name: integrate_polynomial(series[6])
            for name, series in majorants.items()}


def check():
    ctx.prec = 160
    bounds = sixth_moment_bounds()
    assert all(value.is_finite() and value > 0 for value in bounds.values())
    print({name: value.str(12) for name, value in bounds.items()})
    print("DELTA5 DEGREE-PRESERVING MOMENT MAJORANTS; DESIGN ONLY")


if __name__ == "__main__":
    check()
