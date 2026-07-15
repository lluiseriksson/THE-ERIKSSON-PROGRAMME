"""Uniform tail-budget design for 20<=beta<=125 in the five-family lane."""

from fractions import Fraction
from math import factorial

from flint import arb, ctx

import surface_right_edge_five_family_central_design as central
import surface_right_edge_five_family_tail_design as halfline_tail
from surface_bessel_integral_remainder import relative_enclosure_invz
from surface_remainder_arb_jet2 import hull


DELTA_MAX = arb(1)/20
VMIN = arb(201)/1000
SIDE = arb(5)/2


def low_argument_companion(invz, v):
    if invz.upper() > arb(1)/4 or not v > 0:
        raise ValueError("finite-tail companion requires z>=4")
    arel = relative_enclosure_invz(invz, "A", 0, 4)
    brel = relative_enclosure_invz(invz, "B", 0, 4)
    root = 1/((2*arb.pi()).sqrt()*v.sqrt())
    return root*(brel+2*invz*arel), root*arel


def chain(family, order, speed=arb(1), delta_max=DELTA_MAX):
    delta = hull(arb(0), delta_max)
    v = hull(VMIN, arb(2))
    derivatives = [v]+[
        hull(-2*speed**j, 2*speed**j) for j in range(1, order+1)]
    return central.normalized_composite(
        delta, v, derivatives, family, order)


def near_bounds(delta_max=DELTA_MAX):
    saved = central.reduced_values
    central.reduced_values = low_argument_companion
    try:
        delta = hull(arb(0), delta_max)
        v = hull(VMIN, arb(2))
        i0, i1 = low_argument_companion(delta/v, v)
        gaussian = (4*(arb(3)/2).exp()
                    *halfline_tail.gaussian_one_side(arb(4)/3, SIDE))
        u = {}
        for order, weight in (
                (1, 2/arb.pi()), (3, 1/(3*arb.pi())),
                (5, 1/(30*arb.pi()))):
            u[order] = (gaussian*weight*arb(i1.abs_upper())
                        *arb(chain("I1", order,
                                   delta_max=delta_max).abs_upper())/4)
        b = {}
        for order, weight in (
                (2, 1/arb.pi()), (4, 2/(3*arb.pi()))):
            b[order] = (gaussian*weight*arb(i0.abs_upper())
                        *arb(chain("I0", order, arb(1)/2,
                                   delta_max=delta_max).abs_upper()))
        return u, b
    finally:
        central.reduced_values = saved


def crude_chain_constant(order, speed=arb(1), delta_max=DELTA_MAX):
    """Finite-delta composition majorant using this lane's DELTA_MAX."""
    increment = [arb(0)]*(order+1)
    for j in range(1, order+1):
        increment[j] = (delta_max**(j-1)*2*speed**j/factorial(j))
    powers = [[arb(0)]*(order+1) for _ in range(order+1)]
    powers[0][0] = arb(1)
    for k in range(1, order+1):
        powers[k] = central.jet_mul(powers[k-1], increment, order)
    coefficient = sum((powers[k][order]/factorial(k)
                       for k in range(order+1)), arb(0))
    return factorial(order)*coefficient


def far_bounds(delta_max=DELTA_MAX):
    gap = arb(61)/125
    scale = delta_max**(-arb(3)/2)*(-gap/delta_max).exp()
    u = {
        1: scale*crude_chain_constant(1, delta_max=delta_max)/2,
        3: scale*crude_chain_constant(3, delta_max=delta_max)/12,
        5: scale*crude_chain_constant(5, delta_max=delta_max)/120,
    }
    b = {
        2: scale*crude_chain_constant(
            2, arb(1)/2, delta_max=delta_max),
        4: scale*2*crude_chain_constant(
            4, arb(1)/2, delta_max=delta_max)/3,
    }
    return u, b


def budgets(delta_max=DELTA_MAX):
    if (not delta_max > 0
            or arb(delta_max.upper()) > arb(DELTA_MAX.upper())):
        raise ValueError("finite-tail delta endpoint outside contract")
    nu, nb = near_bounds(delta_max)
    fu, fb = far_bounds(delta_max)
    return (nu[1]+fu[1], nu[3]+fu[3], nu[5]+fu[5],
            nb[2]+fb[2], nb[4]+fb[4])


def verify_geometry():
    pi = arb.pi()
    alpha, shift = arb(7)/50, arb(3)/80
    assert SIDE/arb(20).sqrt() < pi/4-alpha-shift/2
    assert 2*(alpha-shift).sin() > VMIN
    amplitude = (2-2*shift.sin()).sqrt()
    sinc_floor = 1-arb(1)/54
    assert amplitude*sinc_floor**2 > arb(4)/3
    assert alpha.sin()+alpha.cos()+shift < arb(117)/100
    assert arb(2).sqrt() > arb(707)/500
    # Prove the deliberately rounded exponent gap in exact rational
    # arithmetic.  Arb equality tests representation, not overlap or exact
    # equality of the underlying real numbers.
    gap = 2*(Fraction(707, 500)-Fraction(117, 100))
    assert gap == Fraction(61, 125)


def main():
    ctx.prec = 140
    verify_geometry()
    values = budgets()
    for name, value in zip(("U0", "U1", "U2", "B0", "B1"), values):
        print(name, "finite_tail", value)
    print("FINITE FIVE-FAMILY TAIL DESIGN PASS; PARAMETER COVER REQUIRED")


if __name__ == "__main__":
    main()
