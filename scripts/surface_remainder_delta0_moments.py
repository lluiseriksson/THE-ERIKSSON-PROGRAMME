"""Regular main-saddle moment integrands through delta=0.

The returned quantities are KD, KF/delta, HDD/delta^2, and HDF/delta^3
after the scaled-coordinate Jacobian.  They are finite at delta=0.  This is
the pointwise K2 carrier; uniform integration and the bilinear cancellation
remain separate obligations.
"""

from dataclasses import dataclass

import mpmath as mp
from flint import arb, ctx

from surface_bessel_integral_remainder import relative_enclosure_invz
from surface_remainder_delta0_geometry import regular_geometry


@dataclass(frozen=True)
class RegularMoments:
    kd: arb
    kf_over_delta: arb
    hdd_over_delta2: arb
    hdf_over_delta3: arb


def delta0_plane_moments(t: arb) -> RegularMoments:
    """Exact full-plane Gaussian coefficients at delta=0."""
    c = (t/4).cos(); cc = 2*c**2-1
    common = 1/(arb(2)*arb.pi()).sqrt()
    kernel_constant = 2*common/(4*c)**(arb(3)/2)
    h_constant = common/(4*c)**(arb(5)/2)
    gaussian_mass = 2*arb.pi()/c
    kd = 2*kernel_constant*gaussian_mass
    hdd = 4*h_constant*gaussian_mass
    ratio = -(2*cc+1)/(2*c)
    return RegularMoments(kd, ratio*kd, hdd, ratio*hdd)


def delta0_bilinear_zero(t: arb) -> arb:
    moments = delta0_plane_moments(t)
    return (moments.kd*moments.hdf_over_delta3
            -moments.kf_over_delta*moments.hdd_over_delta2)


def regular_moment_integrands(delta: arb, t: arb, sigma: arb,
                              tau: arb) -> RegularMoments:
    geometry = regular_geometry(delta, t, sigma, tau)
    c = (t/4).cos()
    common = 1/(arb(2)*arb.pi()).sqrt()
    if geometry.inv_z.upper() <= arb(1)/20:
        order, z0 = 4, 20
    elif geometry.inv_z.upper() <= arb(1)/4:
        # The same integral proof at order zero is monotone from z=4 and
        # bridges outer cutoff cells without ever forming z=infinity.
        order, z0 = 0, 4
    else:
        raise ValueError("regular Bessel lane falls below z=4; subdivide")
    a_relative = relative_enclosure_invz(geometry.inv_z, "A", order, z0)
    b_relative = relative_enclosure_invz(geometry.inv_z, "B", order, z0)
    exponential = geometry.phase.exp()
    kernel = (2*common/(4*c)**(arb(3)/2)
              *geometry.root**(-arb(3)/2)*a_relative*exponential)
    h_regular = (common/(4*c)**(arb(5)/2)
                 *geometry.root**(-arb(5)/2)*b_relative*exponential)
    return RegularMoments(
        kernel*geometry.d_weight,
        kernel*geometry.f_over_delta,
        h_regular*geometry.d_weight**2,
        h_regular*geometry.d_weight*geometry.f_over_delta,
    )


def scalar_direct(delta: mp.mpf, t: mp.mpf, sigma: mp.mpf,
                  tau: mp.mpf) -> dict[str, mp.mpf]:
    beta = 1/delta
    s, alpha = mp.sqrt(delta)*sigma, mp.sqrt(delta)*tau
    c = mp.cos(t/4)
    p, q = mp.sin(s/2)**2, mp.sin(alpha/2)**2
    radius = 2*c*mp.sqrt(1-(p+q-p*q/c**2))
    z = 2*beta*radius
    phase_reference = mp.exp(-4*beta*c)
    kernel = delta*2*beta**mp.mpf("2.5")*mp.besseli(1, z)/z*phase_reference
    h_scaled = delta*beta**mp.mpf("1.5")*mp.besseli(2, z)/z**2*phase_reference
    d_weight = 2*(1-p-q)
    cc = 2*c**2-1
    cos_s, cos_a = mp.cos(s), mp.cos(alpha)
    n = cc*mp.cos(2*s)+cos_a*(cc*cos_s-1+cos_s**2)
    f = n-cc*d_weight
    return {
        "kd": kernel*d_weight,
        "kf_over_delta": kernel*f/delta,
        "hdd_over_delta2": h_scaled*d_weight**2/delta**2,
        "hdf_over_delta3": h_scaled*d_weight*f/delta**3,
    }


def check() -> None:
    ctx.prec = 180
    mp.mp.dps = 80
    box = regular_moment_integrands(
        arb("0.025 +/- 0.025"), arb("2.9"), arb(3), arb(2))
    for delta in (mp.mpf("0.001"), mp.mpf("0.01"), mp.mpf("0.05")):
        direct = scalar_direct(delta, mp.mpf("2.9"), mp.mpf(3), mp.mpf(2))
        for name, value in direct.items():
            assert getattr(box, name).contains(arb(str(value))), (name, value)
    at_zero = regular_moment_integrands(
        arb(0), arb("2.9"), arb(3), arb(2))
    assert all(value.is_finite() for value in at_zero.__dict__.values())
    assert delta0_bilinear_zero(arb("2.9")).contains(arb(0))
    print("regular delta=0 moment integrands contain all direct samples")
    print("full-plane delta=0 bilinear carrier vanishes exactly")


if __name__ == "__main__":
    check()
