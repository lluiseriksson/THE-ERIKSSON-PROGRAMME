"""Centered-form smoke for the weighted-remainder main saddle.

This is design code, not a certificate.  It carries a second-order jet in
delta and first derivatives in the two scaled spatial variables.  The latter
turn the constant interval enclosure of the delta-second coefficient into a
mean-value centered form on each spatial cell.
"""

from __future__ import annotations

from dataclasses import dataclass

import mpmath as mp
from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_carrier_jet import scalar_carrier, scaled_carrier_parts


def A(value: object) -> arb:
    return value if isinstance(value, arb) else arb(str(value))


@dataclass(frozen=True)
class Dual:
    v: arb
    x: arb = arb(0)
    y: arb = arb(0)
    xx: arb = arb(0)
    xy: arb = arb(0)
    yy: arb = arb(0)


def dual(value: object) -> Dual:
    return value if isinstance(value, Dual) else Dual(A(value))


def dadd(a: object, b: object) -> Dual:
    a, b = dual(a), dual(b)
    return Dual(a.v + b.v, a.x + b.x, a.y + b.y,
                a.xx + b.xx, a.xy + b.xy, a.yy + b.yy)


def dneg(a: object) -> Dual:
    a = dual(a)
    return Dual(-a.v, -a.x, -a.y, -a.xx, -a.xy, -a.yy)


def dmul(a: object, b: object) -> Dual:
    a, b = dual(a), dual(b)
    return Dual(
        a.v * b.v,
        a.x * b.v + a.v * b.x,
        a.y * b.v + a.v * b.y,
        a.xx*b.v + 2*a.x*b.x + a.v*b.xx,
        a.xy*b.v + a.x*b.y + a.y*b.x + a.v*b.xy,
        a.yy*b.v + 2*a.y*b.y + a.v*b.yy,
    )


def arb_square(value: arb) -> arb:
    if value.contains(arb(0)):
        return hull(arb(0), arb(value.abs_upper())**2)
    return value**2


def dsquare(a: object) -> Dual:
    a = dual(a)
    return unary(a, arb_square(a.v), 2*a.v, arb(2))


def dinv(a: object) -> Dual:
    a = dual(a)
    value = 1/a.v
    value2 = value*value
    return unary(a, value, -value2, 2*value2*value)


def dscale(a: object, c: object) -> Dual:
    return dmul(a, c)


def unary(a: object, value: arb, derivative: arb,
          second: arb = arb(0)) -> Dual:
    a = dual(a)
    return Dual(
        value, derivative*a.x, derivative*a.y,
        second*arb_square(a.x) + derivative*a.xx,
        second*a.x*a.y + derivative*a.xy,
        second*arb_square(a.y) + derivative*a.yy,
    )


def dsqrt(a: object) -> Dual:
    a = dual(a)
    r = a.v.sqrt()
    inv_r = 1/r
    return unary(a, r, inv_r/2, -(inv_r*inv_r*inv_r)/4)


def dsin(a: object) -> Dual:
    a = dual(a)
    return unary(a, a.v.sin(), a.v.cos(), -a.v.sin())


def dcos(a: object) -> Dual:
    a = dual(a)
    return unary(a, a.v.cos(), -a.v.sin(), -a.v.cos())


@dataclass(frozen=True)
class Jet:
    c0: Dual
    c1: Dual
    c2: Dual


def jet(value: object) -> Jet:
    return value if isinstance(value, Jet) else Jet(dual(value), dual(0), dual(0))


def jadd(a: object, b: object) -> Jet:
    a, b = jet(a), jet(b)
    return Jet(dadd(a.c0, b.c0), dadd(a.c1, b.c1), dadd(a.c2, b.c2))


def jneg(a: object) -> Jet:
    a = jet(a)
    return Jet(dneg(a.c0), dneg(a.c1), dneg(a.c2))


def jmul(a: object, b: object) -> Jet:
    a, b = jet(a), jet(b)
    return Jet(
        dmul(a.c0, b.c0),
        dadd(dmul(a.c0, b.c1), dmul(a.c1, b.c0)),
        dadd(dadd(dmul(a.c0, b.c2), dmul(a.c1, b.c1)),
             dmul(a.c2, b.c0)),
    )


def jsquare(a: object) -> Jet:
    a = jet(a)
    return Jet(
        dsquare(a.c0),
        dmul(2, dmul(a.c0, a.c1)),
        dadd(dmul(2, dmul(a.c0, a.c2)), dsquare(a.c1)),
    )


def jinv(a: object) -> Jet:
    a = jet(a)
    q0 = dinv(a.c0)
    return Jet(
        q0,
        dneg(dmul(a.c1, dmul(q0, q0))),
        dadd(dmul(dsquare(a.c1), dmul(q0, dmul(q0, q0))),
             dneg(dmul(a.c2, dmul(q0, q0)))),
    )


def jscale(a: object, c: object) -> Jet:
    return jmul(a, c)


def jsqrt(a: object) -> Jet:
    a = jet(a)
    r = dsqrt(a.c0)
    return Jet(r, dmul(a.c1, dinv(dmul(2, r))),
               dadd(dmul(a.c2, dinv(dmul(2, r))),
                    dneg(dmul(dsquare(a.c1), dinv(dmul(8, jmul(r, jmul(r, r)).c0))))))


def jsin(a: object) -> Jet:
    a = jet(a)
    s, c = dsin(a.c0), dcos(a.c0)
    return Jet(s, dmul(c, a.c1),
               dadd(dmul(c, a.c2),
                    dneg(dmul(s, dmul(dsquare(a.c1), A(1)/2)))))


def jcos(a: object) -> Jet:
    a = jet(a)
    s, c = dsin(a.c0), dcos(a.c0)
    return Jet(c, dneg(dmul(s, a.c1)),
               dneg(dadd(dmul(s, a.c2),
                         dmul(c, dmul(dsquare(a.c1), A(1)/2)))))


def scaled_ac(z: arb) -> tuple[arb, arb]:
    if z.lower() <= 4:
        raise ValueError("design smoke expects z > 4")
    zl, zh = arb(z.lower()), arb(z.upper())
    av = hull((-zh).exp() * zh.bessel_i(1) / zh,
              (-zl).exp() * zl.bessel_i(1) / zl)
    cv = hull((-zh).exp() * zh.bessel_i(0),
              (-zl).exp() * zl.bessel_i(0))
    return av, cv


def outer_derivatives(z: arb, family: str) -> list[arb]:
    if z.lower() <= 4:
        raise ValueError("endpoint-recurrence path requires z > 4; use entire series")

    def at(x: arb) -> list[arb]:
        a = (-x).exp()*x.bessel_i(1)/x
        c = (-x).exp()*x.bessel_i(0)
        if family == "A":
            return [
                a,
                -(a*x + 2*a - c)/x,
                (2*a*x**2 + 4*a*x + 6*a - 2*c*x - 3*c)/x**2,
                -(4*a*x**3 + 11*a*x**2 + 18*a*x + 24*a
                  - 4*c*x**2 - 9*c*x - 12*c)/x**3,
                (8*a*x**4 + 28*a*x**3 + 63*a*x**2 + 96*a*x + 120*a
                 - 8*c*x**3 - 24*c*x**2 - 48*c*x - 60*c)/x**4,
            ]
        if family == "B":
            b = (-x).exp()*x.bessel_i(2)/x**2
            return [
                b,
                (a*x**2 + 2*a*x + 8*a - c*x - 4*c)/x**3,
                -(2*a*x**3 + 9*a*x**2 + 16*a*x + 40*a
                  - 2*c*x**2 - 8*c*x - 20*c)/x**4,
                (4*a*x**4 + 23*a*x**3 + 72*a*x**2 + 120*a*x + 240*a
                 - 4*c*x**3 - 21*c*x**2 - 60*c*x - 120*c)/x**5,
                -(8*a*x**5 + 56*a*x**4 + 224*a*x**3 + 600*a*x**2
                  + 960*a*x + 1680*a - 8*c*x**4 - 52*c*x**3
                  - 195*c*x**2 - 480*c*x - 840*c)/x**6,
            ]
        raise ValueError(family)

    zl, zh = arb(z.lower()), arb(z.upper())
    vlo, vhi = at(zl), at(zh)
    # Both families are Laplace transforms of positive measures. Hence they
    # are completely monotone: even derivatives are positive/decreasing and
    # odd derivatives are negative/increasing. Endpoint hulls preserve the
    # cancellations in the exact recurrence expressions.
    return [hull(vhi[n], vlo[n]) if n % 2 == 0 else hull(vlo[n], vhi[n])
            for n in range(5)]


def outer_dual(z: Dual, family: str, order: int) -> Dual:
    derivatives = outer_derivatives(z.v, family)
    return unary(z, derivatives[order], derivatives[order + 1],
                 derivatives[order + 2])


def outer_jet(z: Jet, family: str) -> Jet:
    f0 = outer_dual(z.c0, family, 0)
    f1 = outer_dual(z.c0, family, 1)
    f2 = outer_dual(z.c0, family, 2)
    return Jet(f0, dmul(f1, z.c1),
               dadd(dmul(f1, z.c2),
                    dmul(f2, dmul(dsquare(z.c1), A(1)/2))))


def coefficient(delta_value: arb, t_value: arb, sigma: Dual, tau: Dual) -> dict[str, Dual]:
    delta = Jet(dual(delta_value), dual(1), dual(0))
    beta, root_delta = jinv(delta), jsqrt(delta)
    beta2, beta_sqrt = jmul(beta, beta), jsqrt(beta)
    s, alpha = jscale(root_delta, sigma), jscale(root_delta, tau)
    t = t_value
    c, s4 = (t/4).cos(), (t/4).sin()
    ps, pa = jsin(jscale(s, A(1)/2)), jsin(jscale(alpha, A(1)/2))
    cs, ca = jcos(jscale(s, A(1)/2)), jcos(jscale(alpha, A(1)/2))
    p, q = jsquare(ps), jsquare(pa)
    one = jet(1)
    r2 = jadd(jscale(jmul(jsquare(cs), jsquare(ca)), 4*c**2),
              jscale(jmul(p, q), 4*s4**2))
    z = jscale(jmul(beta, jsqrt(r2)), 2)
    ap, bp = outer_jet(z, "A"), outer_jet(z, "B")
    d = jscale(jadd(one, jneg(jadd(p, q))), 2)
    cc = 2*c**2 - 1
    cs, ca, c2s = jcos(s), jcos(alpha), jcos(jscale(s, 2))
    n = jadd(jscale(c2s, cc),
             jmul(ca, jadd(jscale(cs, cc), jadd(jet(-1), jmul(cs, cs)))))
    f = jadd(n, jneg(jscale(d, cc)))
    jac = delta
    kpre = jmul(jscale(jmul(beta2, beta_sqrt), 2), ap)
    hpre = jmul(jmul(beta, beta_sqrt), bp)
    prefs = {
        "muF_main": jmul(jac, jmul(beta, jmul(kpre, f))),
        "nuD_main": jmul(jac, jmul(beta2, jmul(hpre, jmul(d, d)))),
        "nuF_main": jmul(jac, jmul(jmul(beta2, beta), jmul(hpre, jmul(d, f)))),
    }
    phase = jadd(z, jneg(jscale(beta, 4*c)))
    out = {}
    for name, pref in prefs.items():
        out[name] = dadd(pref.c2, dadd(dmul(pref.c1, phase.c1),
            dmul(pref.c0, dadd(phase.c2,
                               dmul(dsquare(phase.c1), A(1)/2)))))
    return out


def mirror_coefficient(delta_value: arb, t_value: arb,
                       sigma: Dual, tau: Dual) -> dict[str, Dual]:
    """Delta-second coefficients for the four judge-scaled mirror moments."""
    delta = Jet(dual(delta_value), dual(1), dual(0))
    beta, root_delta = jinv(delta), jsqrt(delta)
    beta2, beta_sqrt = jmul(beta, beta), jsqrt(beta)
    s, alpha = jscale(root_delta, sigma), jscale(root_delta, tau)
    t = t_value
    c, s4 = (t/4).cos(), (t/4).sin()
    cs2, ca2 = jcos(jscale(s, A(1)/2)), jcos(jscale(alpha, A(1)/2))
    ss2, sa2 = jsin(jscale(s, A(1)/2)), jsin(jscale(alpha, A(1)/2))
    p, q = jsquare(cs2), jsquare(ca2)
    one = jet(1)
    r2 = jadd(jscale(jmul(jsquare(ss2), jsquare(sa2)), 4*c**2),
              jscale(jmul(p, q), 4*s4**2))
    z = jscale(jmul(beta, jsqrt(r2)), 2)
    ap, bp = outer_jet(z, "A"), outer_jet(z, "B")
    d = jscale(jadd(one, jneg(jadd(p, q))), 2)
    cc = 2*c**2 - 1
    cos_so, cos_ao = jneg(jcos(s)), jneg(jcos(alpha))
    n = jadd(jscale(jcos(jscale(s, 2)), cc),
             jmul(cos_ao, jadd(jscale(cos_so, cc),
                               jadd(jet(-1), jmul(cos_so, cos_so)))))
    f = jadd(n, jneg(jscale(d, cc)))
    kpre = jmul(jscale(jmul(beta2, beta_sqrt), 2), ap)
    hpre = jmul(jmul(beta, beta_sqrt), bp)
    prefs = {
        "MD_mirror": jmul(delta, jmul(kpre, d)),
        "MF_mirror": jmul(delta, jmul(kpre, f)),
        "MD2r_mirror": jmul(delta, jmul(beta2, jmul(hpre, jmul(d, d)))),
        "MDFr_mirror": jmul(delta, jmul(beta2, jmul(hpre, jmul(d, f)))),
    }
    phase = jadd(z, jneg(jscale(beta, 4*s4)))
    out = {}
    for name, pref in prefs.items():
        out[name] = dadd(pref.c2, dadd(dmul(pref.c1, phase.c1),
            dmul(pref.c0, dadd(phase.c2,
                               dmul(dsquare(phase.c1), A(1)/2)))))
    return out


def scalar_mirror_carrier(delta: mp.mpf, t: mp.mpf, sigma: mp.mpf,
                          tau: mp.mpf, name: str) -> mp.mpf:
    beta, root_delta = 1/delta, mp.sqrt(delta)
    sl, al = root_delta*sigma, root_delta*tau
    s, alpha = mp.pi-sl, mp.pi-al
    c, s4 = mp.cos(t/4), mp.sin(t/4)
    p, q = mp.sin(s/2)**2, mp.sin(alpha/2)**2
    radius = mp.sqrt(4*c**2*(1-p)*(1-q) + 4*s4**2*p*q)
    z = 2*beta*radius
    kres = 2*beta**mp.mpf("2.5")*(mp.besseli(1, z)/z)*mp.exp(-4*beta*s4)
    hb = beta**mp.mpf("1.5")*(mp.besseli(2, z)/z**2)*mp.exp(-4*beta*s4)
    d = 2*(1-p-q)
    cc = 2*c**2-1
    n = cc*mp.cos(2*s) + mp.cos(alpha)*(cc*mp.cos(s)-1+mp.cos(s)**2)
    f = n-cc*d
    return delta*{
        "MD_mirror": kres*d,
        "MF_mirror": kres*f,
        "MD2r_mirror": beta**2*hb*d**2,
        "MDFr_mirror": beta**2*hb*d*f,
    }[name]


def phase_spatial(delta: arb, t: arb, sigma: Dual, tau: Dual,
                  mirror: bool = False) -> Dual:
    """Common saddle phase with first and second spatial derivatives."""
    root_delta = delta.sqrt()
    s, alpha = dscale(sigma, root_delta), dscale(tau, root_delta)
    c, s4 = (t/4).cos(), (t/4).sin()
    ps, pa = dsin(dscale(s, A(1)/2)), dsin(dscale(alpha, A(1)/2))
    cs, ca = dcos(dscale(s, A(1)/2)), dcos(dscale(alpha, A(1)/2))
    p, q = dsquare(ps), dsquare(pa)
    if mirror:
        r2 = dadd(dscale(dmul(p, q), 4*c**2),
                  dscale(dmul(dsquare(cs), dsquare(ca)), 4*s4**2))
    else:
        r2 = dadd(dscale(dmul(dsquare(cs), dsquare(ca)), 4*c**2),
                  dscale(dmul(p, q), 4*s4**2))
    reference = s4 if mirror else c
    return dadd(dscale(dsqrt(r2), 2/delta), -4*reference/delta)


def phase_residual_spatial(delta: arb, t: arb, sigma: Dual, tau: Dual,
                           mirror: bool = False) -> Dual:
    """Phase after exact removal of its leading scaled Gaussian."""
    phase = phase_spatial(delta, t, sigma, tau, mirror=mirror)
    c, s4 = (t/4).cos(), (t/4).sin()
    p = s4 if mirror else c
    gaussian_deficit = dscale(dadd(dsquare(sigma), dsquare(tau)), p/2)
    return dadd(phase, gaussian_deficit)


def centered_coefficients(delta: arb, t: arb, slo: arb, shi: arb,
                          alo: arb, ahi: arb) -> dict[str, arb]:
    sm, am = (slo + shi)/2, (alo + ahi)/2
    center = coefficient(delta, t, Dual(sm), Dual(am))
    box = coefficient(delta, t, Dual(hull(slo, shi), arb(1)),
                      Dual(hull(alo, ahi), arb(0), arb(1)))
    dx, dy = hull(slo-sm, shi-sm), hull(alo-am, ahi-am)
    return {name: center[name].v + box[name].x*dx + box[name].y*dy
            for name in center}


def check() -> None:
    ctx.prec = 120
    mp.mp.dps = 60
    for family, fn in (
        ("A", lambda z: mp.exp(-z)*mp.besseli(1, z)/z),
        ("B", lambda z: mp.exp(-z)*mp.besseli(2, z)/z**2),
    ):
        for lo, hi in (("5", "6"), ("20", "40"), ("80", "100")):
            box = hull(arb(lo), arb(hi))
            enclosed = outer_derivatives(box, family)
            for sample in (mp.mpf(lo), (mp.mpf(lo)+mp.mpf(hi))/2,
                           mp.mpf(hi)):
                for order in range(5):
                    expected = mp.diff(fn, sample, order)
                    assert enclosed[order].contains(arb(str(expected))), (
                        family, lo, hi, order, enclosed[order], expected)
    delta, t = arb(1)/15, arb("2.9")
    got = centered_coefficients(delta, t, arb("1.0"), arb("1.1"),
                                arb("2.0"), arb("2.1"))
    point = coefficient(delta, t, Dual(arb("1.05"), arb(1)),
                        Dual(arb("2.05"), arb(0), arb(1)))
    old_pref, old_phase = scaled_carrier_parts(delta, t, arb("1.05"),
                                               arb("2.05"))
    for name, pref in old_pref.items():
        expected = (pref.c2 + pref.c1*old_phase.c1
                    + pref.c0*(old_phase.c2 + old_phase.c1**2/2))
        assert point[name].v.overlaps(expected), (name, point[name].v, expected)
    d0, t0 = mp.mpf(1)/15, mp.mpf("2.9")
    s0, a0 = mp.mpf("1.05"), mp.mpf("2.05")

    def scalar_coefficient(name: str, sigma: mp.mpf, tau: mp.mpf) -> mp.mpf:
        def full(d: mp.mpf) -> mp.mpf:
            return d * scalar_carrier(d, t0, mp.sqrt(d)*sigma,
                                      mp.sqrt(d)*tau, name)
        full_c2 = mp.diff(full, d0, 2) / 2
        c, s4 = mp.cos(t0/4), mp.sin(t0/4)
        ss, aa = mp.sqrt(d0)*sigma, mp.sqrt(d0)*tau
        p, q = mp.sin(ss/2)**2, mp.sin(aa/2)**2
        radius = mp.sqrt(4*c**2*(1-p)*(1-q) + 4*s4**2*p*q)
        phase = 2*radius/d0 - 4*c/d0
        return full_c2 / mp.exp(phase)

    for name, value in point.items():
        xx = mp.diff(lambda s: scalar_coefficient(name, s, a0), s0, 2)
        yy = mp.diff(lambda a: scalar_coefficient(name, s0, a), a0, 2)
        xy = mp.diff(lambda s: mp.diff(
            lambda a: scalar_coefficient(name, s, a), a0), s0)
        assert value.xx.contains(arb(str(xx))), (name, "xx", value.xx, xx)
        assert value.xy.contains(arb(str(xy))), (name, "xy", value.xy, xy)
        assert value.yy.contains(arb(str(yy))), (name, "yy", value.yy, yy)
    mirror_point = mirror_coefficient(
        delta, t, Dual(arb("1.05"), arb(1)),
        Dual(arb("2.05"), arb(0), arb(1)))
    beta0 = 1/d0
    c0, s40 = mp.cos(t0/4), mp.sin(t0/4)
    sl0, al0 = mp.sqrt(d0)*s0, mp.sqrt(d0)*a0
    p0, q0 = mp.cos(sl0/2)**2, mp.cos(al0/2)**2
    r0 = mp.sqrt(4*c0**2*(1-p0)*(1-q0) + 4*s40**2*p0*q0)
    mirror_phase = 2*beta0*r0 - 4*beta0*s40
    for name, value in mirror_point.items():
        expected = mp.diff(
            lambda d: scalar_mirror_carrier(d, t0, s0, a0, name), d0, 2
        )/2
        actual_ball = value.v * arb(str(mp.exp(mirror_phase)))
        assert actual_ball.contains(arb(str(expected))), (
            name, actual_ball, expected)

    def scalar_mirror_coefficient(name: str, sigma: mp.mpf,
                                  tau: mp.mpf) -> mp.mpf:
        full_c2 = mp.diff(
            lambda d: scalar_mirror_carrier(d, t0, sigma, tau, name),
            d0, 2,
        )/2
        sl, al = mp.sqrt(d0)*sigma, mp.sqrt(d0)*tau
        p, q = mp.cos(sl/2)**2, mp.cos(al/2)**2
        radius = mp.sqrt(4*c0**2*(1-p)*(1-q) + 4*s40**2*p*q)
        phase = 2*beta0*radius - 4*beta0*s40
        return full_c2/mp.exp(phase)

    for name, value in mirror_point.items():
        xx = mp.diff(lambda s: scalar_mirror_coefficient(name, s, a0), s0, 2)
        yy = mp.diff(lambda a: scalar_mirror_coefficient(name, s0, a), a0, 2)
        xy = mp.diff(lambda s: mp.diff(
            lambda a: scalar_mirror_coefficient(name, s, a), a0), s0)
        assert value.xx.contains(arb(str(xx))), (name, "xx", value.xx, xx)
        assert value.xy.contains(arb(str(xy))), (name, "xy", value.xy, xy)
        assert value.yy.contains(arb(str(yy))), (name, "yy", value.yy, yy)
    direct = coefficient(delta, t,
                         Dual(hull(arb("1.0"), arb("1.1"))),
                         Dual(hull(arb("2.0"), arb("2.1"))))
    for name in got:
        assert got[name].is_finite()
        assert got[name].overlaps(direct[name].v), name
    print("complete-monotone endpoint hulls contain sampled derivatives 0..4")
    print("all seven point coefficients contain independent mp delta derivatives")
    print("all seven spatial Hessians contain independent mp derivatives")
    print({name: value.str(8) for name, value in got.items()})


if __name__ == "__main__":
    check()
