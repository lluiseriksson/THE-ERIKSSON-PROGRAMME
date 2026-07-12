"""Uniform Bessel-companion perturbation on the endpoint delta lane.

The nominal ball-series carrier uses the order-four relative polynomials.
This module bounds the difference from the true A/B companions directly in
value.  Hence no derivative of a remainder bound is taken.
"""

from dataclasses import dataclass

from flint import arb, ctx

from surface_bessel_integral_remainder import uniform_relative_constant


@dataclass(frozen=True)
class MomentErrorCoefficients:
    kd: arb
    kf: arb
    hdd: arb
    hdf: arb


def moment_error_coefficients() -> MomentErrorCoefficients:
    """Return e_M with |M_true-M_poly| <= e_M*delta^5.

    The physical main square has P,Q<=sin(0.6)^2.  Thus the root is at
    least sqrt(1-2 sin(0.6)^2), h=1/z is at most delta times the stated
    coefficient, and the regular phase is bounded by the same Gaussian
    rate used by the separately tested outer-tail lemma.  The global
    bounds |D|<=2 and |F/delta|<=3 sigma^2 follow from |F|<=12P and
    P/delta<=sigma^2/4.
    """
    cmin = arb(2).sqrt()/2
    u = arb("0.6").sin()**2
    sinc = arb("0.6").sin()/arb("0.6")
    rate = 2*cmin*(1-u)*sinc**2/4
    root_min = (1-2*u).sqrt()
    h_coefficient = 1/(4*cmin*root_min)
    common = 1/(2*arb.pi()).sqrt()
    kernel_base = (2*common/(4*cmin)**(arb(3)/2)
                   *root_min**(-arb(3)/2))
    h_base = (common/(4*cmin)**(arb(5)/2)
              *root_min**(-arb(5)/2))
    ca = uniform_relative_constant("A", 4, 20)
    cb = uniform_relative_constant("B", 4, 20)
    quadrant_mass = arb.pi()/(4*rate)
    quadrant_sigma2 = arb.pi()/(8*rate**2)
    factor = arb(4)*h_coefficient**5
    return MomentErrorCoefficients(
        factor*kernel_base*ca*2*quadrant_mass,
        factor*kernel_base*ca*3*quadrant_sigma2,
        factor*h_base*cb*4*quadrant_mass,
        factor*h_base*cb*6*quadrant_sigma2,
    )


def normalized_y_error_coefficient(delta_max: arb, kd_lower: arb,
                                   moment_abs_upper: arb) -> arb:
    """C such that |Y_true-Y_poly| <= C*delta^4 on the lane.

    ``kd_lower`` and ``moment_abs_upper`` refer to the nominal polynomial
    moments on the parameter box.  The returned bound charges both the
    bilinear numerator and the perturbed KD denominator.
    """
    errors = moment_error_coefficients()
    e = max(arb(value.upper()) for value in errors.__dict__.values())
    d5 = delta_max**5
    actual_lower = kd_lower-errors.kd*d5
    if not actual_lower > 0 or not kd_lower > 0:
        raise ValueError("Bessel perturbation does not resolve KD")
    m = moment_abs_upper
    delta_b_coefficient = 4*m*e+2*e**2*d5
    inverse_coefficient = (
        e*(2*m+e*d5)/(actual_lower**2*kd_lower**2)
    )
    cmin = arb(2).sqrt()/2
    return (delta_b_coefficient/actual_lower**2
            +2*m**2*inverse_coefficient)/(2*cmin)


def check() -> None:
    ctx.prec = 160
    errors = moment_error_coefficients()
    assert all(value.is_finite() and value > 0
               for value in errors.__dict__.values())
    coefficient = normalized_y_error_coefficient(
        arb("0.001"), arb(2), arb(10))
    assert coefficient < 1000
    print({name: value.str(12) for name, value in errors.__dict__.items()})
    print("Y companion error <=", coefficient.str(12), "* delta^4")
    print("DELTA0 BESSEL COMPANION VALUE ERROR BOUNDED")


if __name__ == "__main__":
    check()
