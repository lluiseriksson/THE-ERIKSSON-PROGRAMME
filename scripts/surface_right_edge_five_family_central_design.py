"""Two-saddle central design for the five regular G5 families.

The implementation uses the exact scaling in the companion note and the
integral-form Bessel companions.  It intentionally omits the complement of
the two moving saddle charts, so every terminal line says DESIGN ONLY.
"""

from fractions import Fraction
from functools import lru_cache
from math import factorial

from flint import arb, ctx

from surface_bessel_integral_remainder import (
    polynomial_interval, relative_coefficients, uniform_relative_constant,
)
from surface_remainder_arb_jet2 import hull
from surface_right_edge_scaled_paired_design import sinc_y


def ptrim(row):
    while len(row) > 1 and row[-1] == 0:
        row.pop()
    return row


def padd(a, b):
    out = [Fraction(0)]*max(len(a), len(b))
    for i, value in enumerate(a):
        out[i] += value
    for i, value in enumerate(b):
        out[i] += value
    return ptrim(out)


def pscale(a, value):
    return ptrim([value*item for item in a])


def pderivative(a):
    return [Fraction(i)*a[i] for i in range(1, len(a))] or [Fraction(0)]


def pshift2(a):
    return [Fraction(0), Fraction(0)]+a


@lru_cache(maxsize=None)
def derivative_pairs(family, order):
    """Polynomials (a(h),b(h)) with D_z^k I_family=a I0+b I1."""
    pair = ([Fraction(1)], [Fraction(0)]) if family == "I0" else (
        [Fraction(0)], [Fraction(1)])
    out = [pair]
    for _ in range(order):
        a, b = pair
        anew = padd(pscale(pshift2(pderivative(a)), -1), b)
        bnew = padd(a, padd(pscale([Fraction(0)]+b, -1),
                             pscale(pshift2(pderivative(b)), -1)))
        pair = (anew, bnew)
        out.append(pair)
    return out


def peval(coefficients, value):
    out = arb(0)
    for coefficient in reversed(coefficients):
        out = out*value+arb(coefficient.numerator)/coefficient.denominator
    return out


def reduced_i01(invz):
    """Return exp(-z) I_0(z)/sqrt(delta), I_1 analogue; z=v/delta.

    The caller removes sqrt(delta) by supplying v through invz/delta; here
    sqrt(invz/delta)=1/sqrt(v) is passed separately in reduced_values.
    """
    raise RuntimeError("use reduced_values(invz, v)")


def reduced_values(invz, v):
    if not v > 0:
        raise ValueError("central Bessel argument lost positivity")
    # The audited half-line chart geometry proves v>=3/4 and
    # delta<=1/125, hence invz=delta/v<=4/375.  Re-intersect here instead
    # of relying on interval evaluation of the correlated quotient to
    # rediscover those bounds.  This must live in the autonomous backend:
    # an exploratory monkeypatch is not certificate state.
    vlo, vhi = arb(v.lower()), arb(v.upper())
    if vhi < arb(3)/4 or vlo > 2:
        raise ValueError("central Bessel argument contradicts chart geometry")
    v = hull(max(vlo, arb(3)/4), min(vhi, arb(2)))
    zlo, zhi = arb(invz.lower()), arb(invz.upper())
    if zhi < 0 or zlo > arb(4)/375:
        raise ValueError("central inverse-z contradicts chart geometry")
    invz = hull(max(zlo, arb(0)), min(zhi, arb(4)/375))
    if invz.upper() > arb(1)/20:
        raise ValueError("central Bessel argument fell below z=20")
    arel = relative_companion(invz, "A")
    brel = relative_companion(invz, "B")
    root = 1/((2*arb.pi()).sqrt()*v.sqrt())
    i1 = root*arel
    i0 = root*(brel+2*invz*arel)
    return i0, i1


@lru_cache(maxsize=None)
def companion_constant(family, precision):
    del precision
    return uniform_relative_constant(family, 4, 20)


def relative_companion(invz, family):
    polynomial = polynomial_interval(relative_coefficients(family, 4), invz)
    radius = companion_constant(family, ctx.prec)*arb(invz.abs_upper())**5
    return polynomial+radius*arb("0 +/- 1")


def reduced_z_derivatives(invz, v, family, order):
    i0, i1 = reduced_values(invz, v)
    return [peval(a, invz)*i0+peval(b, invz)*i1
            for a, b in derivative_pairs(family, order)]


def jet_mul(a, b, order):
    out = [arb(0)]*(order+1)
    for i in range(min(len(a), order+1)):
        for j in range(min(len(b), order+1-i)):
            out[i+j] += a[i]*b[j]
    return out


def normalized_composite(delta, v, derivatives, family, order):
    """exp(-v/delta)/sqrt(delta) times delta^n D_u^n I_family."""
    invz = delta/v
    fz = reduced_z_derivatives(invz, v, family, order)
    increment = [arb(0)]*(order+1)
    for j in range(1, order+1):
        increment[j] = delta**(j-1)*derivatives[j]/factorial(j)
    powers = [[arb(0)]*(order+1) for _ in range(order+1)]
    powers[0][0] = arb(1)
    for k in range(1, order+1):
        powers[k] = jet_mul(powers[k-1], increment, order)
    series = [arb(0)]*(order+1)
    for k in range(order+1):
        scale = fz[k]/factorial(k)
        for j in range(order+1):
            series[j] += scale*powers[k][j]
    return factorial(order)*series[order]


def cosine_derivatives(base_sin, base_cos, amplitude, speed, order):
    out = [None]*(order+1)
    for j in range(order+1):
        phase = j % 4
        trig = (base_cos, -base_sin, -base_cos, base_sin)[phase]
        out[j] = amplitude*speed**j*trig
    return out


def nonnegative_sqrt(value):
    """Square-root enclosure when a zero-based Arb hull leaks below zero.

    Arb balls cannot represent a closed zero-based interval without a tiny
    negative rounding skirt.  The mathematical contract is value>=0, so at
    the zero face we enclose its square root directly from the upper endpoint.
    """
    if value.lower() > 0:
        return value.sqrt()
    if value.upper() < 0:
        raise ValueError("negative value in nonnegative square-root contract")
    upper = arb(value.upper()).sqrt()
    return hull(arb(0), upper)


def saddle_geometry(delta, shift_rate, q, mirror):
    eta = delta*shift_rate
    se, ce = eta.sin(), eta.cos()
    sign = 1 if mirror else -1
    amplitude = (2+sign*2*se).sqrt()
    sin0 = (1+sign*se)/amplitude
    cos0 = -ce/amplitude if mirror else ce/amplitude
    w = nonnegative_sqrt(delta)*q
    sw, cw = w.sin(), w.cos()
    sinu = sin0*cw+cos0*sw
    cosu = cos0*cw-sin0*sw
    root = (1+sign*se).sqrt()
    sin_over_delta = shift_rate*sinc_y(eta**2)
    offset = sign*2*arb(2).sqrt()*sin_over_delta/(root+1)
    deficit = -amplitude*q**2*sinc_y(delta*q**2/4)**2
    return sinu, cosu, (offset+deficit).exp(), eta


def u_chart_integrand(delta, lam, shift_rate, q, derivative, mirror):
    sinu, cosu, exponential, eta = saddle_geometry(
        delta, shift_rate, q, mirror)
    v1 = 2*sinu
    sin2 = sinu*eta.cos()+cosu*eta.sin()
    cos2 = cosu*eta.cos()-sinu*eta.sin()
    v2 = -2*cos2 if mirror else 2*cos2
    fbar = reduced_values(delta/v1, v1)[1]/2
    amplitude = -2 if mirror else 2
    raw = cosine_derivatives(sin2, cos2, amplitude, arb(1), derivative)
    # v2=+/- 2 cos(u+eta); the array above starts with v2.
    assert raw[0].contains(v2)
    gbar = normalized_composite(delta, v2, raw, "I1", derivative)/2
    if mirror:
        gbar = -gbar
    return exponential*fbar*gbar


def b_chart_integrand(delta, shift_rate, q, derivative, mirror):
    # a=u/2 is the integration variable.  The two saddles have the same
    # phase geometry as the U charts, with cos(a) replacing sin(u).
    eta = delta*shift_rate
    se, ce = eta.sin(), eta.cos()
    sign = 1 if mirror else -1
    amplitude = (2+sign*2*se).sqrt()
    cos0 = (1+sign*se)/amplitude
    sin0 = ce/amplitude if mirror else -ce/amplitude
    w = nonnegative_sqrt(delta)*q
    sw, cw = w.sin(), w.cos()
    sina = sin0*cw+cos0*sw
    cosa = cos0*cw-sin0*sw
    root = (1+sign*se).sqrt()
    sin_over_delta = shift_rate*sinc_y(eta**2)
    offset = sign*2*arb(2).sqrt()*sin_over_delta/(root+1)
    deficit = -amplitude*q**2*sinc_y(delta*q**2/4)**2
    exponential = (offset+deficit).exp()
    v1 = 2*cosa
    angle_sin = sina*eta.cos()+cosa*eta.sin()  # sin(a+eta)
    angle_cos = cosa*eta.cos()-sina*eta.sin()  # cos(a+eta)
    # second k has internal angle a+pi/2+eta, and z differentiation moves
    # that angle at speed 1/2.
    second_sin, second_cos = angle_cos, -angle_sin
    raw = cosine_derivatives(
        second_sin, second_cos, arb(2), arb(1)/2, derivative)
    if mirror:
        raw = [-item for item in raw]
    v2 = raw[0]
    first = reduced_values(delta/v1, v1)[0]
    second = normalized_composite(delta, v2, raw, "I0", derivative)
    return exponential*first*second


def integral_power(lo, hi, power):
    return (hi**(power+1)-lo**(power+1))/(power+1)


def q_sum(evaluator, side, grid):
    if grid < 2 or grid % 2:
        raise ValueError("symmetric q grid must be positive and even")
    # The chart is exactly symmetric.  Evaluate q and -q from the same
    # positive interval so their shared dependency is retained by Arb.
    # Treating the two halves as unrelated boxes is rigorous but destroys
    # the cancellation on which the five-family assembly relies.
    half = grid//2
    width = arb(side)/half
    total = arb(0)
    for index in range(half):
        q = hull(index*width, (index+1)*width)
        total += (evaluator(q)+evaluator(-q))*width
    return total


def integrate_u_family(delta, lam, derivative, side=5, qgrid=80,
                       rgrid=8, thetagrid=4, phigrid=4):
    total = arb(0)
    for ri in range(rgrid):
        rlo = -arb(1)+2*arb(ri)/rgrid
        rhi = -arb(1)+2*arb(ri+1)/rgrid
        theta_count = 1 if derivative < 3 else thetagrid
        phi_count = 1 if derivative < 5 else phigrid
        for ti in range(theta_count):
            tlo, thi = arb(ti)/theta_count, arb(ti+1)/theta_count
            for pi in range(phi_count):
                plo, phi = arb(pi)/phi_count, arb(pi+1)/phi_count
                r = hull(rlo, rhi)
                theta = hull(tlo, thi)
                phiv = hull(plo, phi)
                factor = arb(1)
                rate = r*lam/2
                if derivative >= 3:
                    rate *= theta
                    factor *= integral_power(rlo, rhi, 2)*(thi-tlo)
                else:
                    factor *= rhi-rlo
                if derivative >= 5:
                    rate *= phiv
                    factor = (integral_power(rlo, rhi, 4)
                              *integral_power(tlo, thi, 2)*(phi-plo))
                def evaluate(q):
                    return sum((u_chart_integrand(
                        delta, lam, rate, q, derivative, mirror)
                                for mirror in (False, True)), arb(0))
                total += factor*q_sum(evaluate, side, qgrid)
    coefficient = {1: -1/arb.pi(), 3: -1/(2*arb.pi()),
                   5: -1/(4*arb.pi())}[derivative]
    return coefficient*total


def integrate_b_family(delta, lam, derivative, side=5, qgrid=80,
                       rgrid=8, thetagrid=4, phigrid=None):
    del phigrid
    total = arb(0)
    for ri in range(rgrid):
        rlo = arb(ri)/rgrid
        rhi = arb(ri+1)/rgrid
        theta_count = 1 if derivative == 2 else thetagrid
        for ti in range(theta_count):
            tlo, thi = arb(ti)/theta_count, arb(ti+1)/theta_count
            r, theta = hull(rlo, rhi), hull(tlo, thi)
            rate = r*lam/2
            if derivative == 4:
                rate *= theta
                factor = integral_power(rlo, rhi, 2)*(thi-tlo)
            else:
                factor = rhi-rlo
            def evaluate(q):
                return sum((b_chart_integrand(
                    delta, rate, q, derivative, mirror)
                            for mirror in (False, True)), arb(0))
            total += factor*q_sum(evaluate, side, qgrid)
    return ({2: 1/arb.pi(), 4: 2/arb.pi()}[derivative])*total


def central_families(delta, lam, **kwargs):
    return (
        integrate_u_family(delta, lam, 1, **kwargs),
        integrate_u_family(delta, lam, 3, **kwargs),
        integrate_u_family(delta, lam, 5, **kwargs),
        integrate_b_family(delta, lam, 2, **kwargs),
        integrate_b_family(delta, lam, 4, **kwargs),
    )


def elementary_series(y, family, terms=8):
    # A mathematically nonnegative square may acquire a tiny negative skirt
    # when represented as a zero-based Arb ball.  The series are entire in y.
    if y.upper() < 0 or y.upper() > arb(1)/100:
        raise ValueError("elementary right-edge series outside contract")
    def coefficient(n):
        if family == "s":
            return Fraction((-1)**n, factorial(2*n+1))
        if family == "sy":
            return Fraction((-1)**(n+1)*(n+1), factorial(2*n+3))
        if family == "j":
            return Fraction((-1)**n*2*(n+1), factorial(2*n+3))
        if family == "jy":
            return Fraction((-1)**(n+1)*2*(n+1)*(n+2),
                            factorial(2*n+5))
        raise ValueError(family)
    total = arb(0)
    for n in reversed(range(terms)):
        value = coefficient(n)
        total = total*y+arb(value.numerator)/value.denominator
    omitted = abs(coefficient(terms))
    first = (arb(omitted.numerator)/omitted.denominator
             *arb(y.abs_upper())**terms)
    return total+2*first*arb("0 +/- 1")


def assemble_h(delta, lam, families):
    U0, U1, U2, B0, B1 = families
    y = (delta*lam/2)**2
    s = elementary_series(y, "s")
    sy = elementary_series(y, "sy")
    j = elementary_series(y, "j")
    jy = elementary_series(y, "jy")
    A0 = j*delta**2*U0+2*s*U1
    A1 = jy*delta**4*U0+(j+2*sy)*delta**2*U1+2*s*U2
    P0 = A0*B0+lam**2*(A1*B0-A0*B1)/4
    return P0, P0/(4*B0**2)


def main():
    ctx.prec = 140
    delta, lam = arb(1)/125, arb(1)
    values = central_families(delta, lam, side=5, qgrid=40,
                              rgrid=4, thetagrid=2, phigrid=2)
    print("FIVE-FAMILY CENTRAL", *values, flush=True)
    print("RIGHT-EDGE FIVE-FAMILY CENTRAL DESIGN ONLY; OUTER DOMAIN ABSENT",
          flush=True)


if __name__ == "__main__":
    main()
