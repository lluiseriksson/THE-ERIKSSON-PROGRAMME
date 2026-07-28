"""Second-order spatially centred series integrator for the regular K2 lane.

Design module only.  It keeps normalized delta coefficients through order five
while integrating each symmetric spatial cell by its midpoint value and a
rigorous Hessian remainder.  Linear spatial terms integrate to zero.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import comb, factorial

from flint import arb, arb_series, ctx

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_series_design import PREC, assemble_y_derivatives


TERMS = 32


def aq(value):
    if isinstance(value, Fraction):
        return arb(value.numerator)/arb(value.denominator)
    return value if isinstance(value, arb) else arb(str(value))


def series(value):
    return value if isinstance(value, arb_series) else arb_series([aq(value)], PREC)


def pm1():
    return arb("0 +/- 1")


def root2_floor():
    u = arb("0.6").sin()**2
    return (1-u)**2/2


def apply_constant_floor(value, floor):
    """Intersect only the constant coefficient with a proved floor."""
    row = value.coeffs()+[arb(0)]*PREC
    band = hull(floor, arb(row[0].upper()))
    row[0] = row[0].intersection(band)
    return arb_series(row, PREC)


def apply_root2_floor(value):
    return apply_constant_floor(value, root2_floor())


@dataclass(frozen=True)
class SDual:
    v: arb_series
    x: arb_series
    y: arb_series
    xx: arb_series
    xy: arb_series
    yy: arb_series


def sd(value, x=0, y=0, xx=0, xy=0, yy=0):
    if isinstance(value, SDual):
        return value
    return SDual(*(series(item) for item in (value, x, y, xx, xy, yy)))


def add(a, b):
    a, b = sd(a), sd(b)
    return SDual(*(x+y for x, y in zip(a.__dict__.values(), b.__dict__.values())))


def neg(a):
    a = sd(a)
    return SDual(*(-x for x in a.__dict__.values()))


def mul(a, b):
    a, b = sd(a), sd(b)
    return SDual(
        a.v*b.v,
        a.x*b.v+a.v*b.x,
        a.y*b.v+a.v*b.y,
        a.xx*b.v+2*a.x*b.x+a.v*b.xx,
        a.xy*b.v+a.x*b.y+a.y*b.x+a.v*b.xy,
        a.yy*b.v+2*a.y*b.y+a.v*b.yy,
    )


def unary(a, value, first, second):
    a = sd(a); value, first, second = map(series, (value, first, second))
    return SDual(
        value,
        first*a.x,
        first*a.y,
        second*a.x*a.x+first*a.xx,
        second*a.x*a.y+first*a.xy,
        second*a.y*a.y+first*a.yy,
    )


def inv(a):
    a = sd(a); value = 1/a.v
    return unary(a, value, -value*value, 2*value*value*value)


def sqrt(a):
    a = sd(a); root = a.v.sqrt()
    # Form negative powers from the already certified positive factor.  Direct
    # interval multiplication of three wide copies of ``root`` can lose the
    # positive lower endpoint even though each factor is strictly positive.
    inv_root = 1/root
    return unary(a, root, inv_root/2, -inv_root*inv_root*inv_root/4)


def exp(a):
    a = sd(a); value = a.v.exp()
    return unary(a, value, value, value)


def coefficient(alpha_n):
    return arb((-1)**alpha_n*2**(2*alpha_n+1))/arb(factorial(2*alpha_n+2))


def falling(value, order):
    return factorial(value)//factorial(value-order) if value >= order else 0


def _absolute_term(n, k, derivative, base_abs, x_abs):
    if n < k or n+1 < derivative:
        return arb(0)
    return (arb(2**(2*n+1))/arb(factorial(2*n+2))*arb(comb(n, k))
            *base_abs**(n-k)*arb(falling(n+1, derivative))
            *x_abs**(n+1-derivative))


def p_over_delta(base, sigma):
    """Spatial dual of x*sinc(sqrt(delta*x))^2, x=sigma^2/4."""
    sigma = sd(sigma)
    x = mul(mul(sigma, sigma), arb(1)/4)
    base_abs, x_abs = arb(base.abs_upper()), arb(x.v.coeffs()[0].abs_upper())
    derivatives = []
    for derivative in range(3):
        row = []
        for k in range(PREC):
            total = arb(0)
            # The derivative of x^(n+1) vanishes when n+1 < derivative.
            # Starting earlier would evaluate 0*x^(-1) on origin-touching
            # spatial boxes, which Arb correctly turns into an indeterminate
            # value even though the mathematical term is absent.
            for n in range(max(k, derivative-1, 0), TERMS):
                total += (coefficient(n)*arb(comb(n, k))*base**(n-k)
                          *arb(falling(n+1, derivative))
                          *x.v.coeffs()[0]**(n+1-derivative))
            tail = sum((_absolute_term(n, k, derivative, base_abs, x_abs)
                        for n in range(TERMS, 200)), arb(0))
            next_term = _absolute_term(200, k, derivative, base_abs, x_abs)
            after = _absolute_term(201, k, derivative, base_abs, x_abs)
            ratio = after/next_term if next_term > 0 else arb(0)
            if not ratio < arb(1)/2:
                raise ValueError("sinc spatial tail is not contractive")
            tail += next_term/(1-ratio)
            row.append(total+tail*pm1())
        derivatives.append(arb_series(row, PREC))
    return unary(x, derivatives[0], derivatives[1], derivatives[2])


def relative_polynomial(h, family):
    out = sd(0)
    for value in reversed(relative_coefficients(family, 4)):
        out = add(mul(out, h), aq(value))
    return out


def moment_duals(base, t, sigma, tau):
    d = sd(arb_series([base, arb(1)], PREC))
    p, q = p_over_delta(base, sigma), p_over_delta(base, tau)
    c = (t/4).cos(); c2 = c**2; cc = 2*c2-1
    w = add(add(p, q), mul(-1/c2, mul(d, mul(p, q))))
    radicand = add(1, neg(mul(d, w)))
    radicand = SDual(apply_root2_floor(radicand.v), radicand.x, radicand.y,
                      radicand.xx, radicand.xy, radicand.yy)
    root = sqrt(radicand)
    root = SDual(apply_constant_floor(root.v, root2_floor().sqrt()),
                 root.x, root.y, root.xx, root.xy, root.yy)
    phase = mul(-4*c, mul(w, inv(add(1, root))))
    h = mul(d, inv(mul(4*c, root)))
    dweight = mul(2, add(1, neg(mul(d, add(p, q)))))
    bracket = add(
        add(add(mul(-2*cc, mul(d, p)), mul(-cc, mul(d, q))), 2*cc+1),
        add(mul(2, mul(mul(d, d), mul(p, q))),
            add(neg(mul(d, p)), mul(-2, mul(d, q)))))
    fover = mul(-4, mul(p, bracket))
    common = 1/(2*arb.pi()).sqrt()
    root_half = sqrt(root)
    inv_root = inv(root)
    inv_root_half = inv(root_half)
    kernel = mul(2*common/(4*c)**(arb(3)/2),
                 mul(mul(inv_root, inv_root_half), relative_polynomial(h, "A")))
    hregular = mul(common/(4*c)**(arb(5)/2),
                   mul(mul(mul(inv_root, inv_root), inv_root_half),
                       relative_polynomial(h, "B")))
    exponential = exp(phase)
    return {
        "kd": mul(mul(kernel, dweight), exponential),
        "kf": mul(mul(kernel, fover), exponential),
        "hdd": mul(mul(hregular, mul(dweight, dweight)), exponential),
        "hdf": mul(mul(hregular, mul(dweight, fover)), exponential),
    }


def _coeff(value, order):
    values = value.coeffs()
    return values[order] if order < len(values) else arb(0)


def centered_cell(base, t, slo, shi, alo, ahi):
    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    center = moment_duals(base, t, sd(sm, 1), sd(am, 0, 1))
    box = moment_duals(base, t, sd(hull(slo, shi), 1),
                       sd(hull(alo, ahi), 0, 1))
    area = 4*(shi-slo)*(ahi-alo)
    out = {}
    for name in center:
        row = []
        for order in range(PREC):
            error = (arb(_coeff(box[name].xx, order).abs_upper())*rx**2/2
                     +arb(_coeff(box[name].xy, order).abs_upper())*rx*ry
                     +arb(_coeff(box[name].yy, order).abs_upper())*ry**2/2)
            row.append(area*(_coeff(center[name].v, order)+error*pm1()))
        out[name] = row
    return out


def integrate_moments(base, t, grid, side=12):
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("kd", "kf", "hdd", "hdf")}
    width = arb(side)/grid
    for i in range(grid):
        for j in range(grid):
            values = centered_cell(base, t, width*i, width*(i+1),
                                   width*j, width*(j+1))
            for name, row in values.items():
                for order, value in enumerate(row):
                    totals[name][order] += value
    return {name: arb_series(row, PREC) for name, row in totals.items()}


def integrate(base, t, grid, side=12):
    moments = integrate_moments(base, t, grid, side)
    return moments, assemble_y_derivatives(moments, t)


if __name__ == "__main__":
    ctx.prec = 140
    lane, t = hull(arb(0), arb("0.004")), hull(arb("3.14"), arb.pi())
    for grid in (8, 16, 32):
        moments = integrate_moments(lane, t, grid)
        kd0 = moments["kd"].coeffs()[0]
        print("CENTERED REGULAR grid", grid, "KD0", kd0, flush=True)
        if kd0 > 0:
            y = assemble_y_derivatives(moments, t)
            print("CENTERED REGULAR grid", grid, "Y3", y.coeffs()[3],
                  flush=True)
    print("CENTERED REGULAR DESIGN NEGATIVE: momentwise Hessian bounds "
          "lose determinant cancellation")
