"""Order-parametric Bessel-companion value error for future K2 heads.

The sealed order-four endpoint dependency remains byte-invariant in
``surface_remainder_delta0_companion_error.py``.  This separate module is
the extension point for higher exact heads.
"""

from flint import arb

from surface_bessel_integral_remainder import uniform_relative_constant
from surface_remainder_delta0_companion_error import MomentErrorCoefficients


def moment_error_coefficients(order: int) -> MomentErrorCoefficients:
    """Return ``e_M`` with ``|Delta M| <= e_M delta^(order+1)``."""
    if order < 0:
        raise ValueError("negative companion order")
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
    ca = uniform_relative_constant("A", order, 20)
    cb = uniform_relative_constant("B", order, 20)
    quadrant_mass = arb.pi()/(4*rate)
    quadrant_sigma2 = arb.pi()/(8*rate**2)
    factor = arb(4)*h_coefficient**(order+1)
    return MomentErrorCoefficients(
        factor*kernel_base*ca*2*quadrant_mass,
        factor*kernel_base*ca*3*quadrant_sigma2,
        factor*h_base*cb*4*quadrant_mass,
        factor*h_base*cb*6*quadrant_sigma2,
    )


def normalized_y_error_coefficient(delta_max: arb, kd_lower: arb,
                                   moment_abs_upper: arb,
                                   order: int) -> arb:
    """Return ``C`` with normalized-Y error at most ``C delta^order``."""
    errors = moment_error_coefficients(order)
    e = max(arb(value.upper()) for value in errors.__dict__.values())
    moment_error = delta_max**(order+1)
    actual_lower = kd_lower-e*moment_error
    if not actual_lower > 0 or not kd_lower > 0:
        raise ValueError("Bessel perturbation does not resolve KD")
    m = moment_abs_upper
    delta_b_coefficient = 4*m*e+2*e**2*moment_error
    inverse_coefficient = (
        e*(2*m+e*moment_error)/(actual_lower**2*kd_lower**2))
    cmin = arb(2).sqrt()/2
    return (delta_b_coefficient/actual_lower**2
            +2*m**2*inverse_coefficient)/(2*cmin)
