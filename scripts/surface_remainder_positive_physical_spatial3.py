"""Cubic-spatial centered integrator for the positive K2 lane.

The quadratic Taylor polynomial of the fully calibrated integrand is
integrated exactly against the affine phase.  Only its total-degree-three
spatial remainder is charged by absolute values.
"""

from math import factorial

from flint import arb, arb_series

from surface_bessel_integral_remainder import relative_coefficients
from surface_remainder_arb_jet2 import hull
from surface_remainder_positive_physical_series_design import PREC, aq
from surface_remainder_spatial_jet3 import (
    Jet3, jadd, jcos, jexp, jinv, jet, jmul, jneg, jscale, jsin, jsqrt,
    variable_x, variable_y,
)


def sconst(value):
    return [jet(value)]+[jet(0) for _ in range(PREC-1)]


def sadd(a, b):
    return [jadd(x, y) for x, y in zip(a, b)]


def sneg(a):
    return [jneg(x) for x in a]


def sscale(a, value):
    return [jscale(x, value) for x in a]


def smul(a, b):
    out = [jet(0) for _ in range(PREC)]
    for n in range(PREC):
        for k in range(n+1):
            out[n] = jadd(out[n], jmul(a[k], b[n-k]))
    return out


def sinv(a):
    out = [jet(0) for _ in range(PREC)]
    out[0] = jinv(a[0])
    for n in range(1, PREC):
        total = jet(0)
        for k in range(1, n+1):
            total = jadd(total, jmul(a[k], out[n-k]))
        out[n] = jneg(jmul(out[0], total))
    return out


def ssqrt(a):
    out = [jet(0) for _ in range(PREC)]
    out[0] = jsqrt(a[0])
    for n in range(1, PREC):
        total = a[n]
        for k in range(1, n):
            total = jadd(total, jneg(jmul(out[k], out[n-k])))
        out[n] = jmul(total, jinv(jmul(2, out[0])))
    return out


def sexp(a):
    out = [jet(0) for _ in range(PREC)]
    out[0] = jexp(a[0])
    for n in range(1, PREC):
        total = jet(0)
        for k in range(1, n+1):
            total = jadd(total, jmul(k, jmul(a[k], out[n-k])))
        out[n] = jscale(total, arb(1)/n)
    return out


def spoly(a, coefficients):
    out = sconst(0)
    for coefficient in reversed(coefficients):
        out = sadd(smul(out, a), sconst(aq(coefficient)))
    return out


def physical_moment_parts(delta: arb, t: arb, s: Jet3, alpha: Jet3):
    ds = [jet(delta), jet(1)]+[jet(0) for _ in range(PREC-2)]
    ds_inv = sinv(ds)
    c, s4 = (t/4).cos(), (t/4).sin()
    p = jmul(jsin(jscale(s, arb(1)/2)), jsin(jscale(s, arb(1)/2)))
    q = jmul(jsin(jscale(alpha, arb(1)/2)),
             jsin(jscale(alpha, arb(1)/2)))
    radius2 = jadd(
        jscale(jmul(jadd(1, jneg(p)), jadd(1, jneg(q))), 4*c**2),
        jscale(jmul(p, q), 4*s4**2))
    radius = jsqrt(radius2)
    h = sscale(ds, jinv(jscale(radius, 2)))
    phase = smul(sadd(sconst(jscale(radius, 2)), sconst(-4*c)), ds_inv)
    common = 1/(2*arb.pi()).sqrt()
    root3 = jmul(jscale(radius, 2), jsqrt(jscale(radius, 2)))
    root5 = jmul(jscale(radius, 2), root3)
    kernel = smul(
        sscale(smul(ds_inv, spoly(h, relative_coefficients("A", 5))),
               2*common), sconst(jinv(root3)))
    hkernel = smul(
        sscale(smul(ds, spoly(h, relative_coefficients("B", 5))), common),
        sconst(jinv(root5)))
    dweight = jscale(jadd(1, jneg(jadd(p, q))), 2)
    cc = 2*c**2-1
    cos_s, cos_a = jcos(s), jcos(alpha)
    n = jadd(jscale(jcos(jscale(s, 2)), cc),
             jmul(cos_a, jadd(jscale(cos_s, cc),
                              jadd(-1, jmul(cos_s, cos_s)))))
    fluctuation = jadd(n, jscale(dweight, -cc))
    return {
        "KD": sscale(kernel, dweight),
        "KF": sscale(kernel, fluctuation),
        "HDD": sscale(hkernel, jmul(dweight, dweight)),
        "HDF": sscale(hkernel, jmul(dweight, fluctuation)),
    }, phase


def linear_moment(gradient: arb, width: arb, power: int,
                  terms: int = 36) -> arb:
    """Rigorous integral of x^power exp(gradient*x) on a centred interval."""
    a = width/2
    total = arb(0)
    for k in range(terms):
        if (power+k) % 2 == 0:
            total += (2*a**(power+k+1)*gradient**k
                      /arb(factorial(k)*(power+k+1)))
    magnitude = arb(gradient.abs_upper())
    first = (2*a**(power+terms+1)*magnitude**terms
             /arb(factorial(terms)*(power+terms+1)))
    ratio = magnitude*a/arb(terms+1)
    if not ratio < arb(1)/2:
        raise ValueError("linear-moment Taylor tail is not contractive")
    return total+first/(1-ratio)*arb("0 +/- 1")


def _remove_constant_and_linear(phase: Jet3, gx: arb, gy: arb) -> Jet3:
    coefficients = dict(phase.coefficients)
    coefficients[0, 0] = arb(0)
    coefficients[1, 0] = phase.get(1, 0)-gx
    coefficients[0, 1] = phase.get(0, 1)-gy
    return Jet3(coefficients)


def centered_cell(delta: arb, t: arb, slo: arb, shi: arb,
                  alo: arb, ahi: arb, calibration):
    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    center_prefactors, center_phase = physical_moment_parts(
        delta, t, variable_x(sm), variable_y(am))
    box_prefactors, box_phase = physical_moment_parts(
        delta, t, variable_x(hull(slo, shi)),
        variable_y(hull(alo, ahi)))
    qseries = [jet(value) for value in calibration]
    for prefactors in (center_prefactors, box_prefactors):
        prefactors["KF"] = sadd(prefactors["KF"],
                                sneg(smul(qseries, prefactors["KD"])))
        prefactors["HDF"] = sadd(prefactors["HDF"],
                                 sneg(smul(qseries, prefactors["HDD"])))
    center_correction = [jet(0)]+center_phase[1:]
    box_correction = [jet(0)]+box_phase[1:]
    center = {name: smul(value, sexp(center_correction))
              for name, value in center_prefactors.items()}
    box = {name: smul(value, sexp(box_correction))
           for name, value in box_prefactors.items()}
    pc, pb = center_phase[0], box_phase[0]
    gx, gy = arb(pc.get(1, 0).mid()), arb(pc.get(0, 1).mid())
    center_residual = jexp(_remove_constant_and_linear(pc, gx, gy))
    box_residual = jexp(_remove_constant_and_linear(pb, gx, gy))
    mx = [linear_moment(gx, 2*rx, order) for order in range(3)]
    my = [linear_moment(gy, 2*ry, order) for order in range(3)]
    spatial = mx[0]*my[0]
    out = {}
    for name in center:
        coefficients = []
        for cc, bb in zip(center[name], box[name]):
            fc, fb = jmul(cc, center_residual), jmul(bb, box_residual)
            quadratic = sum((fc.get(i, j)*mx[i]*my[j]
                             for degree in range(3)
                             for i in range(degree+1)
                             for j in (degree-i,)), arb(0))
            remainder = sum((arb(fb.get(i, j).abs_upper())*rx**i*ry**j
                             for i in range(4) for j in range(4-i)
                             if i+j == 3), arb(0))*spatial
            coefficients.append(4*pc.get(0, 0).exp()
                                *(quadratic+remainder*arb("0 +/- 1")))
        out[name] = coefficients
    return out


def integrate_moments(delta: arb, t: arb, grid: int, calibration):
    totals = {name: [arb(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    width = arb("1.2")/grid
    for i in range(grid):
        for j in range(grid):
            values = centered_cell(delta, t, width*i, width*(i+1),
                                   width*j, width*(j+1), calibration)
            for name, coefficients in values.items():
                for order, value in enumerate(coefficients):
                    totals[name][order] += value
    return {name: arb_series(values, PREC) for name, values in totals.items()}
