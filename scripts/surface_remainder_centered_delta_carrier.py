"""Fourth-order centred-delta jets for the fixed-physical K4 carriers.

This module is a design successor to the wide whole-box ``Jet2`` lane.  It
does not integrate a carrier or discharge K4.  It supplies ordinary delta
derivatives through order four so a terminal integrator can retain the
centre value of the second derivative and charge its variation by Taylor's
theorem on the whole delta box.

The scaled-Bessel compositions use three explicit rigorous branches: the
positive entire-series enclosure on ``0 <= z <= 4``, the isolated Taylor
remainder enclosure on ``4 <= z <= 20``, and the integral-form half-line
enclosure on ``z >= 20``.  Cells crossing a branch boundary are still
rejected and must be subdivided; no interpolation between regimes is used.
"""

from math import factorial

from flint import arb

from surface_bessel_entire_lowz import entire_outer_derivatives
from surface_bessel_gap_taylor import derivative_enclosures as gap_outer_derivatives
from surface_bessel_integral_remainder import derivative_enclosures
from surface_remainder_tjet import TJet, tjet
from surface_remainder_arb_jet2 import hull


R0_SQUARED = arb(16)
R1_SQUARED = arb(100)
DELTA_R2 = arb(84)


def scaled_bessel_jet(z: TJet, family: str) -> TJet:
    """Compose a delta jet with rigorous outer derivatives 0 through 4."""
    if z.v.upper() <= 4:
        derivatives = entire_outer_derivatives(z.v, family, order=4)
    elif z.v.lower() >= 4 and z.v.upper() <= 20:
        derivatives = gap_outer_derivatives(z.v, family, order=4)
    elif z.v.lower() >= 20:
        derivatives = derivative_enclosures(z.v, family, order=4)
    else:
        raise ValueError(
            "centred K4 Bessel cell lies in unproved gap 4<z<20")
    normalized = [value/arb(factorial(order))
                  for order, value in enumerate(derivatives)]
    return z._compose(normalized)


def cutoff_jet(delta: TJet, s: arb, alpha: arb) -> TJet:
    """Jet of chi((s^2+alpha^2)/delta) on one cutoff piece."""
    u = (s**2+alpha**2)/delta
    if bool(u.v <= R0_SQUARED):
        return tjet(1)
    if bool(u.v >= R1_SQUARED):
        return tjet(0)
    if not bool((u.v > R0_SQUARED) and (u.v < R1_SQUARED)):
        raise ValueError("centred K4 cell crosses a cutoff junction")
    q = (u-R0_SQUARED)/DELTA_R2
    return 1-10*q**3+15*q**4-6*q**5


def complement_weight(delta: TJet, s: arb, alpha: arb,
                      inside_physical_square: bool) -> TJet:
    return tjet(1 if inside_physical_square else 0)-cutoff_jet(
        delta, s, alpha)


def main_carriers(delta_value, t_value, s_value, alpha_value):
    """Judge-scaled main carriers in fixed physical coordinates."""
    delta = (delta_value if isinstance(delta_value, TJet)
             else tjet(delta_value, 1))
    beta = 1/delta
    beta2 = beta**2
    beta_sqrt = beta.sqrt()
    beta32, beta52 = beta*beta_sqrt, beta2*beta_sqrt
    # Keep a TJet supplied by a t-box caller.  Coercing it to an Arb would
    # silently discard the parameter derivatives needed for a rigorous
    # whole-box t Taylor charge.
    t = t_value if isinstance(t_value, (arb, TJet)) else arb(str(t_value))
    s = s_value if isinstance(s_value, arb) else arb(str(s_value))
    alpha = (alpha_value if isinstance(alpha_value, arb)
             else arb(str(alpha_value)))
    c, s4 = (t/4).cos(), (t/4).sin()
    p, q = (s/2).sin()**2, (alpha/2).sin()**2
    # Exact deficit form.  Forming ``2*radius*beta-4*c*beta`` loses the
    # shared leading term on a delta box.  Since
    # radius = 2*c*sqrt(1-w), w=p+q-p*q/c^2, rationalization removes that
    # cancellation before interval evaluation.
    w = p+q-p*q/c**2
    root = (1-w).sqrt()
    radius = 2*c*root
    z = 2*radius*beta
    phase = -4*c*beta*w/(1+root)
    exponential = phase.exp()
    kernel = 2*beta52*scaled_bessel_jet(z, "A")*exponential
    hb = beta32*scaled_bessel_jet(z, "B")*exponential
    d = 2*(1-p-q)
    cc = 2*c**2-1
    cos_s, cos_a = s.cos(), alpha.cos()
    # Exact cancellation-preserving factorization of ``n-cc*d``.  Forming
    # the two terms separately loses the quadratic zero at s=0 on Arb boxes.
    f = (cos_s-1)*(cc*(2*cos_s+1)
                   +cos_a*(cos_s+cc+1))
    return {
        "muF_main": beta*kernel*f,
        "nuD_main": beta2*hb*d**2,
        "nuF_main": beta2*beta*hb*d*f,
    }


def mirror_carriers(delta_value, t_value, s_distance_value,
                    alpha_distance_value):
    """Judge-scaled mirror carriers in fixed physical coordinates."""
    delta = (delta_value if isinstance(delta_value, TJet)
             else tjet(delta_value, 1))
    beta = 1/delta
    beta2 = beta**2
    beta_sqrt = beta.sqrt()
    beta32, beta52 = beta*beta_sqrt, beta2*beta_sqrt
    t = t_value if isinstance(t_value, (arb, TJet)) else arb(str(t_value))
    sd = (s_distance_value if isinstance(s_distance_value, arb)
          else arb(str(s_distance_value)))
    ad = (alpha_distance_value if isinstance(alpha_distance_value, arb)
          else arb(str(alpha_distance_value)))
    c, s4 = (t/4).cos(), (t/4).sin()
    ps, pa = (sd/2).cos()**2, (ad/2).cos()**2
    pd, qd = 1-ps, 1-pa
    # Mirror analogue of the same exact rationalization:
    # radius = 2*s4*sqrt(1-w), w=pd+qd-pd*qd/s4^2.
    w = pd+qd-pd*qd/s4**2
    root = (1-w).sqrt()
    radius = 2*s4*root
    z = 2*radius*beta
    phase = -4*s4*beta*w/(1+root)
    exponential = phase.exp()
    kernel = 2*beta52*scaled_bessel_jet(z, "A")*exponential
    hb = beta32*scaled_bessel_jet(z, "B")*exponential
    d = 2*(1-ps-pa)
    cc = 2*c**2-1
    cos_s, cos_a = -sd.cos(), -ad.cos()
    # Mirror counterpart of the same exact factorization, now in the
    # positive variables x=cos(sd), y=cos(ad); the first factor is x+1.
    x, y = sd.cos(), ad.cos()
    f = (x+1)*(cc*(2*x-1)+y*(cc+1-x))
    return {
        "MD_mirror": kernel*d,
        "MF_mirror": kernel*f,
        "MD2r_mirror": beta2*hb*d**2,
        "MDFr_mirror": beta2*hb*d*f,
    }


def scaled_main_carriers(delta_value, t_value, sigma_value, tau_value):
    """Judge-scaled main carriers after ``s=sqrt(delta)*sigma``.

    The Jacobian is included.  The exact rationalized phase keeps this
    representation regular on every strictly positive delta box.
    """
    delta = (delta_value if isinstance(delta_value, TJet)
             else tjet(delta_value, 1))
    beta = 1/delta
    beta2 = beta**2
    beta_sqrt = beta.sqrt()
    beta32, beta52 = beta*beta_sqrt, beta2*beta_sqrt
    root_delta = delta.sqrt()
    sigma = (sigma_value if isinstance(sigma_value, arb)
             else arb(str(sigma_value)))
    tau = (tau_value if isinstance(tau_value, arb)
           else arb(str(tau_value)))
    s, alpha = root_delta*sigma, root_delta*tau
    t = t_value if isinstance(t_value, (arb, TJet)) else arb(str(t_value))
    c = (t/4).cos()
    p, q = (s/2).sin()**2, (alpha/2).sin()**2
    w = p+q-p*q/c**2
    root = (1-w).sqrt()
    z = 4*c*beta*root
    phase = -4*c*beta*w/(1+root)
    kernel = 2*beta52*scaled_bessel_jet(z, "A")*phase.exp()
    hb = beta32*scaled_bessel_jet(z, "B")*phase.exp()
    d = 2*(1-p-q)
    cc = 2*c**2-1
    cos_s, cos_a = s.cos(), alpha.cos()
    f = (cos_s-1)*(cc*(2*cos_s+1)
                   +cos_a*(cos_s+cc+1))
    return {
        "muF_main": delta*beta*kernel*f,
        "nuD_main": delta*beta2*hb*d**2,
        "nuF_main": delta*beta2*beta*hb*d*f,
    }


def scaled_mirror_carriers(delta_value, t_value, sigma_value, tau_value):
    """Judge-scaled mirror carriers with the scaled-coordinate Jacobian."""
    delta = (delta_value if isinstance(delta_value, TJet)
             else tjet(delta_value, 1))
    beta = 1/delta
    beta2 = beta**2
    beta_sqrt = beta.sqrt()
    beta32, beta52 = beta*beta_sqrt, beta2*beta_sqrt
    root_delta = delta.sqrt()
    sigma = (sigma_value if isinstance(sigma_value, arb)
             else arb(str(sigma_value)))
    tau = (tau_value if isinstance(tau_value, arb)
           else arb(str(tau_value)))
    sd, ad = root_delta*sigma, root_delta*tau
    t = t_value if isinstance(t_value, (arb, TJet)) else arb(str(t_value))
    c, s4 = (t/4).cos(), (t/4).sin()
    pd, qd = (sd/2).sin()**2, (ad/2).sin()**2
    ps, pa = 1-pd, 1-qd
    w = pd+qd-pd*qd/s4**2
    root = (1-w).sqrt()
    z = 4*s4*beta*root
    phase = -4*s4*beta*w/(1+root)
    kernel = 2*beta52*scaled_bessel_jet(z, "A")*phase.exp()
    hb = beta32*scaled_bessel_jet(z, "B")*phase.exp()
    d = 2*(1-ps-pa)
    cc = 2*c**2-1
    cos_s, cos_a = -sd.cos(), -ad.cos()
    x, y = sd.cos(), ad.cos()
    f = (x+1)*(cc*(2*x-1)+y*(cc+1-x))
    return {
        "MD_mirror": delta*kernel*d,
        "MF_mirror": delta*kernel*f,
        "MD2r_mirror": delta*beta2*hb*d**2,
        "MDFr_mirror": delta*beta2*hb*d*f,
    }


def direct_scaled_centered_delta_cell(delta_lo: arb, delta_hi: arb,
                                      t: arb, slo: arb, shi: arb,
                                      alo: arb, ahi: arb):
    """Centred-delta half-second derivative on a fixed scaled cell."""
    if not delta_lo > 0 or delta_hi < delta_lo:
        raise ValueError("scaled centred K4 delta cell must be positive")
    from surface_remainder_core_l2_arb import (
        cell_bounds, mirror_gaussian_cell_bounds,
    )
    from surface_remainder_complement_l3_smoke import NAMES

    midpoint, radius = (delta_lo+delta_hi)/2, (delta_hi-delta_lo)/2
    retained_main, _ = cell_bounds(
        midpoint, t, slo, shi, alo, ahi)
    retained_mirror = mirror_gaussian_cell_bounds(
        midpoint, t, slo, shi, alo, ahi)
    # Both independent routines return the ordinary second derivative on
    # one quadrant (their internal factor two restores c2 -> f'').  Divide
    # by two and multiply by four quadrants: net factor two.
    retained = {name: 2*value for name, value in retained_main.items()}
    retained.update({name: 2*value
                     for name, value in retained_mirror.items()})
    sbox, abox = hull(slo, shi), hull(alo, ahi)
    center_delta = tjet(midpoint, 1)
    whole_delta = tjet(hull(delta_lo, delta_hi), 1)
    center = scaled_main_carriers(center_delta, t, sbox, abox)
    center.update(scaled_mirror_carriers(center_delta, t, sbox, abox))
    whole = scaled_main_carriers(whole_delta, t, sbox, abox)
    whole.update(scaled_mirror_carriers(whole_delta, t, sbox, abox))
    area = 4*(shi-slo)*(ahi-alo)
    sign = arb("0 +/- 1")
    out = {}
    for name in NAMES:
        half_variation = (
            radius*arb(center[name].d3.abs_upper())/2
            +radius**2*arb(whole[name].d4.abs_upper())/4)
        out[name] = retained[name]+area*half_variation*sign
    return out


def weighted_carriers(delta_value, t_value, s_value, alpha_value,
                      mirror: bool, inside_physical_square: bool):
    """Multiply all carriers by the exact fixed-domain complement weight."""
    delta = (delta_value if isinstance(delta_value, TJet)
             else tjet(delta_value, 1))
    weight = complement_weight(
        delta,
        s_value if isinstance(s_value, arb) else arb(str(s_value)),
        alpha_value if isinstance(alpha_value, arb) else arb(str(alpha_value)),
        inside_physical_square,
    )
    # Outside the fixed physical square, cells beyond the cutoff support have
    # an exact zero complement weight.  Do not evaluate the Bessel carrier on
    # those cells: its asymptotic jet can legitimately be undefined there
    # (for example when a mirror radius leaves the z>=20 contract), and
    # multiplying ``0 * nan`` is not a valid interval operation.  Returning
    # the exact zero jet is the algebraic value of the weighted integrand.
    if all(component == 0 for component in weight.derivatives()):
        return {name: tjet(0) for name in (
            ("MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror")
            if mirror else ("muF_main", "nuD_main", "nuF_main"))}
    carriers = (mirror_carriers(delta, t_value, s_value, alpha_value)
                if mirror else
                main_carriers(delta, t_value, s_value, alpha_value))
    return {name: weight*value for name, value in carriers.items()}


def second_derivative_enclosure(center: TJet, whole_box: TJet,
                                radius: arb) -> arb:
    """Enclose f'' on a centred delta box using a fourth derivative."""
    if radius < 0:
        raise ValueError("delta radius must be nonnegative")
    sign = arb("0 +/- 1")
    return (center.d2
            +radius*arb(center.d3.abs_upper())*sign
            +radius**2*arb(whole_box.d4.abs_upper())/2*sign)


def centered_delta_cell(delta_lo: arb, delta_hi: arb, t: arb,
                        slo: arb, shi: arb, alo: arb, ahi: arb,
                        inside_physical_square: bool):
    """Integrate one spatial cell with separate delta centre/box tracks.

    The retained centre second derivative uses the independently implemented
    spatial midpoint enclosure from the earlier K4 smoke.  Third and fourth
    derivatives are bounded on the whole spatial cell by this module.  A
    cutoff-crossing spatial cell is rejected and must be subdivided.
    Returned values store one half of the ordinary second derivative, matching
    the literal weighted-judge convention.
    """
    if not arb(0) < delta_lo <= delta_hi:
        raise ValueError("centred K4 delta cell must be positive and ordered")
    from surface_remainder_complement_l3_smoke import centered_cell, NAMES

    midpoint, radius = (delta_lo+delta_hi)/2, (delta_hi-delta_lo)/2
    retained = centered_cell(
        midpoint, t, slo, shi, alo, ahi, inside_physical_square)
    sbox, abox = hull(slo, shi), hull(alo, ahi)
    center_delta = tjet(midpoint, 1)
    whole_delta = tjet(hull(delta_lo, delta_hi), 1)
    center = weighted_carriers(
        center_delta, t, sbox, abox, mirror=False,
        inside_physical_square=inside_physical_square)
    center.update(weighted_carriers(
        center_delta, t, sbox, abox, mirror=True,
        inside_physical_square=inside_physical_square))
    whole = weighted_carriers(
        whole_delta, t, sbox, abox, mirror=False,
        inside_physical_square=inside_physical_square)
    whole.update(weighted_carriers(
        whole_delta, t, sbox, abox, mirror=True,
        inside_physical_square=inside_physical_square))
    area = 4*(shi-slo)*(ahi-alo)
    sign = arb("0 +/- 1")
    out = {}
    for name in NAMES:
        half_variation = (
            radius*arb(center[name].d3.abs_upper())/2
            +radius**2*arb(whole[name].d4.abs_upper())/4)
        out[name] = retained[name]+area*half_variation*sign
    return out


def centered_physical_second_cell(delta: arb, t: arb,
                                  slo: arb, shi: arb,
                                  alo: arb, ahi: arb):
    """Integrate the half-second derivative on one fixed physical cell.

    This is the direct ``integral_D f`` lane.  It is algebraically equal to
    localized core plus fixed-domain complement, but contains no artificial
    cutoff and therefore no cutoff-junction dependency.  The midpoint value
    and the spatial Hessian enclosure are supplied by the independent Jet2
    implementation.
    """
    from surface_remainder_centered_prefactor import Dual, physical_carriers

    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    sbox, abox = hull(slo, shi), hull(alo, ahi)
    center = physical_carriers(
        delta, t, Dual(sm, arb(1)), Dual(am, arb(0), arb(1)))
    center.update(physical_carriers(
        delta, t, Dual(sm, arb(1)), Dual(am, arb(0), arb(1)),
        mirror=True))
    box = physical_carriers(
        delta, t, Dual(sbox, arb(1)), Dual(abox, arb(0), arb(1)))
    box.update(physical_carriers(
        delta, t, Dual(sbox, arb(1)), Dual(abox, arb(0), arb(1)),
        mirror=True))
    area = 4*(shi-slo)*(ahi-alo)
    sign = arb("0 +/- 1")
    out = {}
    for name in center:
        coefficient = center[name].c2
        error = (arb(box[name].c2.xx.abs_upper())*rx**2/2
                 +arb(box[name].c2.xy.abs_upper())*rx*ry
                 +arb(box[name].c2.yy.abs_upper())*ry**2/2)
        out[name] = area*(coefficient.v+error*sign)
    return out


def direct_centered_delta_cell(delta_lo: arb, delta_hi: arb, t: arb,
                               slo: arb, shi: arb,
                               alo: arb, ahi: arb):
    """Direct fixed-physical carrier enclosure on a positive delta box.

    The centre track retains the independently implemented spatially
    integrated half-second derivative.  Third and fourth ordinary delta
    derivatives then control its variation over the whole box.  Unlike
    :func:`centered_delta_cell`, this exact lane has no localization weight.
    """
    if not delta_lo > 0 or delta_hi < delta_lo:
        raise ValueError("direct centred K4 delta cell must be positive")
    from surface_remainder_complement_l3_smoke import NAMES

    midpoint, radius = (delta_lo+delta_hi)/2, (delta_hi-delta_lo)/2
    retained = centered_physical_second_cell(
        midpoint, t, slo, shi, alo, ahi)
    sbox, abox = hull(slo, shi), hull(alo, ahi)
    center_delta = tjet(midpoint, 1)
    whole_delta = tjet(hull(delta_lo, delta_hi), 1)
    center = main_carriers(center_delta, t, sbox, abox)
    center.update(mirror_carriers(center_delta, t, sbox, abox))
    whole = main_carriers(whole_delta, t, sbox, abox)
    whole.update(mirror_carriers(whole_delta, t, sbox, abox))
    area = 4*(shi-slo)*(ahi-alo)
    sign = arb("0 +/- 1")
    out = {}
    for name in NAMES:
        half_variation = (
            radius*arb(center[name].d3.abs_upper())/2
            +radius**2*arb(whole[name].d4.abs_upper())/4)
        out[name] = retained[name]+area*half_variation*sign
    return out
