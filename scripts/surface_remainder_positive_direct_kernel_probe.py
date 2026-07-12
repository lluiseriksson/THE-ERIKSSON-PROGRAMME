"""Four-variable pointwise determinant smoke for the positive K2 lane."""

from itertools import product
from math import factorial

from flint import arb, ctx

from surface_bessel_integral_remainder import relative_coefficients
import surface_remainder_positive_pairwise_probe as scalar
import surface_remainder_positive_physical_spatial3 as p5
import surface_remainder_positive_t_centered as denominator
import surface_remainder_spatial_jet_nd as nd
from surface_remainder_tjet import tjet


PREC = p5.PREC
ZERO = (0, 0, 0, 0)


def sconst(value): return [nd.jet(value)]+[nd.jet(0) for _ in range(PREC-1)]
def sadd(a, b): return [nd.jadd(x, y) for x, y in zip(a, b)]
def sneg(a): return [nd.jneg(x) for x in a]
def sscale(a, value): return [nd.jscale(x, value) for x in a]


def smul(a, b):
    return [sum_jet((nd.jmul(a[k], b[n-k]) for k in range(n+1)))
            for n in range(PREC)]


def sum_jet(values):
    out = nd.jet(0)
    for value in values: out = nd.jadd(out, value)
    return out


def sinv(a):
    out = [nd.jet(0) for _ in range(PREC)]
    out[0] = nd.jinv(a[0])
    for n in range(1, PREC):
        out[n] = nd.jneg(nd.jmul(out[0], sum_jet(
            nd.jmul(a[k], out[n-k]) for k in range(1, n+1))))
    return out


def ssqrt(a):
    out = [nd.jet(0) for _ in range(PREC)]
    out[0] = nd.jsqrt(a[0])
    for n in range(1, PREC):
        total = a[n]
        for k in range(1, n): total = nd.jadd(total, nd.jneg(nd.jmul(out[k], out[n-k])))
        out[n] = nd.jmul(total, nd.jinv(nd.jmul(2, out[0])))
    return out


def sexp(a):
    out = [nd.jet(0) for _ in range(PREC)]
    out[0] = nd.jexp(a[0])
    for n in range(1, PREC):
        total = sum_jet(nd.jmul(k, nd.jmul(a[k], out[n-k]))
                        for k in range(1, n+1))
        out[n] = nd.jscale(total, arb(1)/n)
    return out


def spoly(a, coefficients):
    out = sconst(0)
    for coefficient in reversed(coefficients):
        out = sadd(smul(out, a), sconst(p5.aq(coefficient)))
    return out


def primitives(delta, t, s, a):
    ds = [nd.jet(delta), nd.jet(1)]+[nd.jet(0)]*(PREC-2)
    ds_inv = sinv(ds)
    c, s4 = (t/4).cos(), (t/4).sin()
    sp = nd.jmul(nd.jsin(nd.jscale(s, arb(1)/2)), nd.jsin(nd.jscale(s, arb(1)/2)))
    ap = nd.jmul(nd.jsin(nd.jscale(a, arb(1)/2)), nd.jsin(nd.jscale(a, arb(1)/2)))
    radius2 = nd.jadd(
        nd.jscale(nd.jmul(nd.jadd(1, nd.jneg(sp)), nd.jadd(1, nd.jneg(ap))), 4*c**2),
        nd.jscale(nd.jmul(sp, ap), 4*s4**2))
    value = radius2.get(ZERO)
    radius2 = nd.JetND(dict(radius2.coefficients), 4, 5)
    radius2.coefficients[ZERO] = value.intersection(p5.hull(
        p5.physical_radius2_floor(), arb(value.upper())))
    radius = nd.jsqrt(radius2)
    h = sscale(ds, nd.jinv(nd.jscale(radius, 2)))
    phase = smul(sadd(sconst(nd.jscale(radius, 2)), sconst(-4*c)), ds_inv)
    common = 1/(2*arb.pi()).sqrt()
    root3 = nd.jmul(nd.jscale(radius, 2), nd.jsqrt(nd.jscale(radius, 2)))
    root5 = nd.jmul(nd.jscale(radius, 2), root3)
    kernel = smul(sscale(smul(ds_inv, spoly(h, relative_coefficients("A", 6))),
                         2*common), sconst(nd.jinv(root3)))
    hkernel = smul(sscale(smul(ds, spoly(h, relative_coefficients("B", 6))), common),
                  sconst(nd.jinv(root5)))
    d = nd.jscale(nd.jadd(1, nd.jneg(nd.jadd(sp, ap))), 2)
    cc = 2*c**2-1
    cos_s, cos_a = nd.jcos(s), nd.jcos(a)
    n = nd.jadd(nd.jscale(nd.jcos(nd.jscale(s, 2)), cc),
                nd.jmul(cos_a, nd.jadd(nd.jscale(cos_s, cc),
                                       nd.jadd(-1, nd.jmul(cos_s, cos_s)))))
    f = nd.jadd(n, nd.jscale(d, -cc))
    return kernel, hkernel, d, f, phase


def remove_affine(phase, gradients):
    coefficients = dict(phase.coefficients)
    coefficients[ZERO] = arb(0)
    for axis, gradient in enumerate(gradients):
        unit = tuple(1 if k == axis else 0 for k in range(4))
        coefficients[unit] = phase.get(unit)-gradient
    return nd.JetND(coefficients, 4, 5)


def direct_cell(delta, t, lows, highs):
    mids = [(a+b)/2 for a, b in zip(lows, highs)]
    radii = [(b-a)/2 for a, b in zip(lows, highs)]
    cv = [nd.variable(value, axis) for axis, value in enumerate(mids)]
    bv = [nd.variable(p5.hull(a, b), axis) for axis, (a, b) in enumerate(zip(lows, highs))]
    def build(v):
        kx, hx, dx, fx, px = primitives(delta, t, v[0], v[1])
        ky, hy, dy, fy, py = primitives(delta, t, v[2], v[3])
        first = nd.jadd(nd.jmul(dx, fy), nd.jneg(nd.jmul(fx, dy)))
        second = sadd(smul(kx, sconst(nd.jmul(hy, dy))),
                      sneg(smul(ky, sconst(nd.jmul(hx, dx)))))
        return sscale(second, first), sadd(px, py)
    cp, cphase = build(cv); bp, bphase = build(bv)
    center = smul(cp, sexp([nd.jet(0)]+cphase[1:]))
    box = smul(bp, sexp([nd.jet(0)]+bphase[1:]))
    pc, pb = cphase[0], bphase[0]
    gradients = []
    for axis in range(4):
        unit = tuple(1 if k == axis else 0 for k in range(4))
        gradients.append(arb(pc.get(unit).mid()))
    cr, br = nd.jexp(remove_affine(pc, gradients)), nd.jexp(remove_affine(pb, gradients))
    moments = [[p5.linear_moment(g, 2*r, power) for power in range(5)]
               for g, r in zip(gradients, radii)]
    mass = product_values(row[0] for row in moments)
    row = []
    for cc, bb in zip(center, box):
        fc, fb = nd.jmul(cc, cr), nd.jmul(bb, br)
        retained = arb(0); remainder = arb(0)
        for index in nd.indices(4, 5):
            factor = product_values(moments[k][power] for k, power in enumerate(index))
            if sum(index) < 5: retained += fc.get(index)*factor
            elif sum(index) == 5:
                remainder += arb(fb.get(index).abs_upper())*product_values(
                    radii[k]**power for k, power in enumerate(index))*mass
        row.append(8*pc.get(ZERO).exp()*(retained+remainder*arb("0 +/- 1")))
    return row


def product_values(values):
    out = arb(1)
    for value in values: out *= value
    return out


def main():
    ctx.prec = 100
    delta, radius, t, grid = arb("0.0495"), arb("0.0005"), arb("1.01"), 2
    width = arb("1.2")/grid
    squares = [(width*i, width*(i+1), width*j, width*(j+1))
               for i in range(grid) for j in range(grid)]
    numerator = [arb(0) for _ in range(PREC)]
    for left in squares:
        for right in squares:
            lows = (left[0], left[2], right[0], right[2])
            highs = (left[1], left[3], right[1], right[3])
            row = direct_cell(delta, t, lows, highs)
            numerator = scalar.scalar_add(numerator, row)
    moments, _, _ = denominator.parallel_uniform_moments(delta, t, grid=8, workers=4)
    kd = scalar.scalar_row(moments["KD"])
    d = [delta, arb(1)]+[arb(0)]*(PREC-2)
    factor = scalar.scalar_mul(scalar.scalar_inv(scalar.scalar_mul(
        scalar.scalar_mul(scalar.scalar_mul(d, d), d), d)),
        scalar.scalar_mul(scalar.scalar_inv(kd), scalar.scalar_inv(kd)))
    y = [4*x for x in scalar.scalar_mul(numerator, factor)]
    head = [value.v for value in denominator.exact_head(delta, tjet(t, 1, 0))]
    residual = scalar.scalar_evaluate_through(
        scalar.scalar_add(y, scalar.scalar_neg(head)), p5.hull(-radius, radius))
    print("DIRECT KERNEL grid", grid, "residual", residual.abs_upper())
    print("DIRECT KERNEL PROBE DESIGN ONLY")


if __name__ == "__main__": main()
