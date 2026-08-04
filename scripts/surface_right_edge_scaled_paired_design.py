"""Design integrator pairing the two right-edge saddle charts.

The purpose of this file is to test the regularized moment assembly before a
production contract is frozen.  It integrates only fixed central squares;
the complementary-domain majorant is intentionally absent, so its output is
never a certificate.
"""

from dataclasses import dataclass
from math import factorial

from flint import arb, ctx

from surface_bessel_integral_remainder import relative_enclosure_invz
from surface_remainder_arb_jet2 import hull
from surface_remainder_delta0_geometry import sinc_squared_y
from surface_remainder_delta0_geometry import sinc_squared_dual
from surface_remainder_centered_prefactor import (
    Dual, dadd, dinv, dmul, dsqrt, dsquare, dual, unary,
)
from surface_remainder_core_l2_arb import (
    linear_first_moment, linear_integral,
)


def sinc_y(y: arb, terms: int = 18) -> arb:
    """Enclose sinc(sqrt(y)) as an entire series in nonnegative y."""
    if y.upper() < 0:
        raise ValueError("sinc argument square must be nonnegative")
    ymax = arb(y.abs_upper())
    total = arb(0)
    for n in range(terms):
        total += arb((-1) ** n) * y**n / factorial(2*n+1)
    first = ymax**terms / factorial(2*terms+1)
    ratio = ymax / arb((2*terms+3)*(2*terms+2))
    if not ratio < arb(1)/2:
        raise ValueError("sinc tail is not contractive")
    return total + first/(1-ratio)*arb("0 +/- 1")


@dataclass(frozen=True)
class Moments:
    kd: arb
    kf: arb
    kt: arb
    hdd: arb
    hdf: arb

    def __add__(self, other):
        return Moments(*(a+b for a, b in zip(
            self.__dict__.values(), other.__dict__.values())))

    def scale(self, value):
        return Moments(*(value*a for a in self.__dict__.values()))


def dual_power(value: Dual, power: arb) -> Dual:
    return unary(value, value.v**power, power*value.v**(power-1),
                 power*(power-1)*value.v**(power-2))


def parameters(delta: arb, lam: arb):
    a = delta*lam/4
    r = arb(2).sqrt()/2
    c = r*(a.cos()+a.sin())
    s = r*(a.cos()-a.sin())
    half = delta*lam/2
    c_over = lam/2*sinc_y(half**2)
    suppression = (-arb(2).sqrt()*lam*sinc_y(a**2)).exp()
    return c, s, c_over, suppression


def chart(delta: arb, lam: arb, sigma: arb, tau: arb,
          mirror: bool) -> Moments:
    c, s, c_over, suppression = parameters(delta, lam)
    saddle = s if mirror else c
    sigma2, tau2 = sigma**2, tau**2
    p_over = sigma2/4*sinc_squared_y(delta*sigma2/4)
    q_over = tau2/4*sinc_squared_y(delta*tau2/4)
    w_over = p_over+q_over-delta*p_over*q_over/saddle**2
    root = (1-delta*w_over).sqrt()
    phase = -4*saddle*w_over/(1+root)
    inv_z = delta/(4*saddle*root)
    if inv_z.upper() <= arb(1)/20:
        order, z0 = 4, 20
    elif inv_z.upper() <= arb(1)/4:
        order, z0 = 0, 4
    else:
        raise ValueError("paired chart falls below z=4")
    a_rel = relative_enclosure_invz(inv_z, "A", order, z0)
    b_rel = relative_enclosure_invz(inv_z, "B", order, z0)
    common = 1/(2*arb.pi()).sqrt()
    kernel = (2*common/(4*saddle)**(arb(3)/2)
              *root**(-arb(3)/2)*a_rel)
    hkernel = (common/(4*saddle)**(arb(5)/2)
               *root**(-arb(5)/2)*b_rel)
    p, q = delta*p_over, delta*q_over
    if mirror:
        d = 2*(p+q-1)
        f_over = 4*(p-1)*(
            delta*(2*c_over*p_over+c_over*q_over
                   +2*p_over*q_over)-c_over-p_over)
        t_weight = 4*(p-1)*(2*p+q-1)
        factor = suppression
    else:
        d = 2*(1-p-q)
        f_over = -4*p_over*(
            1+delta*(2*c_over-p_over-2*q_over)
            +delta**2*(-2*c_over*p_over-c_over*q_over
                        +2*p_over*q_over))
        t_weight = 4*p*(2*p+q-2)
        factor = arb(1)
    exponential = phase.exp()*factor
    return Moments(
        kernel*d*exponential,
        kernel*f_over*exponential,
        kernel*t_weight*exponential,
        hkernel*d**2*exponential,
        hkernel*d*f_over*exponential,
    )


def chart_dual_parts(delta: arb, lam: arb, sigma: Dual, tau: Dual,
                     mirror: bool):
    """Spatial two-jet prefactors, local phase, and inverse argument."""
    sigma, tau = dual(sigma), dual(tau)
    c, s, c_over, suppression = parameters(delta, lam)
    saddle = s if mirror else c
    sigma2, tau2 = dsquare(sigma), dsquare(tau)
    py, qy = dmul(delta/4, sigma2), dmul(delta/4, tau2)
    p_over = dmul(dmul(sigma2, arb(1)/4), sinc_squared_dual(py))
    q_over = dmul(dmul(tau2, arb(1)/4), sinc_squared_dual(qy))
    w_over = dadd(dadd(p_over, q_over),
                  dmul(-delta/saddle**2, dmul(p_over, q_over)))
    root = dsqrt(dadd(1, dmul(-delta, w_over)))
    phase = dmul(-4*saddle, dmul(w_over, unary(
        dadd(1, root), 1/(1+root.v), -1/(1+root.v)**2,
        2/(1+root.v)**3)))
    inv_z = dmul(delta/(4*saddle), dinv(root))
    common = 1/(2*arb.pi()).sqrt()
    kernel = dmul(2*common/(4*saddle)**(arb(3)/2),
                  dual_power(root, -arb(3)/2))
    hkernel = dmul(common/(4*saddle)**(arb(5)/2),
                   dual_power(root, -arb(5)/2))
    p, q = dmul(delta, p_over), dmul(delta, q_over)
    if mirror:
        d = dmul(2, dadd(dadd(p, q), -1))
        f_over = dmul(4, dmul(dadd(p, -1), dadd(
            dmul(delta, dadd(
                dadd(dmul(2*c_over, p_over), dmul(c_over, q_over)),
                dmul(2, dmul(p_over, q_over)))),
            dadd(-c_over, dmul(-1, p_over)))))
        t_weight = dmul(4, dmul(dadd(p, -1),
                                dadd(dadd(dmul(2, p), q), -1)))
        factor = suppression
    else:
        d = dmul(2, dadd(1, dmul(-1, dadd(p, q))))
        bracket = dadd(1, dadd(
            dmul(delta, dadd(dadd(2*c_over, dmul(-1, p_over)),
                             dmul(-2, q_over))),
            dmul(delta**2, dadd(
                dadd(dmul(-2*c_over, p_over),
                     dmul(-c_over, q_over)),
                dmul(2, dmul(p_over, q_over))))))
        f_over = dmul(-4, dmul(p_over, bracket))
        t_weight = dmul(4, dmul(p,
                                dadd(dadd(dmul(2, p), q), -2)))
        factor = arb(1)
    return {
        "kd": dmul(factor, dmul(kernel, d)),
        "kf": dmul(factor, dmul(kernel, f_over)),
        "kt": dmul(factor, dmul(kernel, t_weight)),
        "hdd": dmul(factor, dmul(hkernel, dmul(d, d))),
        "hdf": dmul(factor, dmul(hkernel, dmul(d, f_over))),
    }, phase, inv_z


def centered_chart_cell(delta: arb, lam: arb, slo: arb, shi: arb,
                        alo: arb, ahi: arb, mirror: bool) -> Moments:
    sigma, tau = hull(slo, shi), hull(alo, ahi)
    sm, am = (slo+shi)/2, (alo+ahi)/2
    sw, tw = shi-slo, ahi-alo
    center_g, center_phase, _ = chart_dual_parts(
        delta, lam, Dual(sm, arb(1)), Dual(am, arb(0), arb(1)), mirror)
    box_g, box_phase, box_inv_z = chart_dual_parts(
        delta, lam, Dual(sigma, arb(1)), Dual(tau, arb(0), arb(1)), mirror)
    gs, gt = arb(center_phase.x.mid()), arb(center_phase.y.mid())
    rx, ry = sw/2, tw/2
    radius = (
        arb((center_phase.x-gs).abs_upper())*rx
        + arb((center_phase.y-gt).abs_upper())*ry
        + arb(box_phase.xx.abs_upper())*rx**2/2
        + arb(box_phase.xy.abs_upper())*rx*ry
        + arb(box_phase.yy.abs_upper())*ry**2/2
    )
    exp_remainder = (radius*arb("0 +/- 1")).exp()
    spatial = linear_integral(gs, sw)*linear_integral(gt, tw)
    first_sigma = linear_first_moment(gs, sw)*linear_integral(gt, tw)
    first_tau = linear_integral(gs, sw)*linear_first_moment(gt, tw)
    phase_error = exp_remainder-1
    if box_inv_z.v.upper() <= arb(1)/20:
        order, z0 = 4, 20
    elif box_inv_z.v.upper() <= arb(1)/4:
        order, z0 = 0, 4
    else:
        raise ValueError("centered paired chart falls below z=4")
    relatives = {
        "A": relative_enclosure_invz(box_inv_z.v, "A", order, z0),
        "B": relative_enclosure_invz(box_inv_z.v, "B", order, z0),
    }
    out = []
    for name in ("kd", "kf", "kt", "hdd", "hdf"):
        gc, gb = center_g[name], box_g[name]
        affine = gc.v*spatial+gc.x*first_sigma+gc.y*first_tau
        hessian = (arb(gb.xx.abs_upper())*rx**2/2
                   +arb(gb.xy.abs_upper())*rx*ry
                   +arb(gb.yy.abs_upper())*ry**2/2)
        affine_abs = (arb(gc.v.abs_upper())
                      +arb(gc.x.abs_upper())*rx
                      +arb(gc.y.abs_upper())*ry)
        error = (hessian*exp_remainder+affine_abs*phase_error)*spatial
        family = "A" if name in ("kd", "kf", "kt") else "B"
        out.append(center_phase.v.exp()*relatives[family]
                   *(affine+error*arb("0 +/- 1"))*4)
    return Moments(*out)


def integrate_centered(delta: arb, lam: arb, side: int = 8,
                       grid: int = 32) -> Moments:
    return integrate_centered_chart(delta, lam, side, grid, False) + \
        integrate_centered_chart(delta, lam, side, grid, True)


def integrate_centered_chart(delta: arb, lam: arb, side: int,
                             grid: int, mirror: bool) -> Moments:
    totals = Moments(*(arb(0) for _ in range(5)))
    width = arb(side)/grid
    for i in range(grid):
        for j in range(grid):
            bounds = (width*i, width*(i+1), width*j, width*(j+1))
            totals = totals + centered_chart_cell(
                delta, lam, *bounds, mirror)
    return totals


def integrate(delta: arb, lam: arb, side: int = 8,
              grid: int = 64) -> Moments:
    totals = Moments(*(arb(0) for _ in range(5)))
    width = arb(side)/grid
    for i in range(grid):
        for j in range(grid):
            sigma = hull(width*i, width*(i+1))
            tau = hull(width*j, width*(j+1))
            pair = chart(delta, lam, sigma, tau, False) + chart(
                delta, lam, sigma, tau, True)
            totals = totals + pair.scale(4*width**2)
    return totals


def normalized_h(m: Moments, lam: arb, delta: arb) -> arb:
    """Exact central-square assembly of -E_t/lambda in scaled units."""
    s_half = (delta*lam/2).cos()  # sin(t/2)=cos(lambda*delta/2)
    bilinear = m.kd*m.hdf-m.kf*m.hdd
    return (s_half/(2*lam)*(1+m.kt/m.kd)
            +2*s_half/lam*bilinear/m.kd**2)


def main():
    ctx.prec = 140
    for delta in (arb(0), arb(1)/500, arb(1)/125):
        for lam in (arb("0.1"), arb("0.5"), arb(1), arb("1.5")):
            moments = integrate(delta, lam)
            print("PAIR", "delta", delta, "lambda", lam,
                  "Hcentral", normalized_h(moments, lam, delta), flush=True)
    print("PAIRED RIGHT-EDGE CENTRAL DESIGN ONLY; OUTER DOMAIN ABSENT",
          flush=True)


if __name__ == "__main__":
    main()
