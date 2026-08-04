"""Analytic tail-budget design for the scaled five-family G5 lane.

The near tail uses the integral-form Bessel companions on the two central
angular charts.  The far angular exterior uses only the integer-order Bessel
integral representation and an exact phase gap.  This remains DESIGN until
the angular partition and every constant are frozen in a production ledger.
"""

from math import factorial

from flint import arb, ctx

import surface_right_edge_five_family_central_design as central
from surface_remainder_arb_jet2 import hull


DELTA = arb(1)/125
LAMBDA = arb(3)/2
VMIN = arb(3)/4


def generic_reduced_chain(family, order, speed=arb(1)):
    delta = hull(arb(0), DELTA)
    v = hull(VMIN, arb(2))
    derivatives = [v]
    for j in range(1, order+1):
        bound = 2*speed**j
        derivatives.append(hull(-bound, bound))
    return central.normalized_composite(
        delta, v, derivatives, family, order)


def gaussian_one_side(c, side):
    return (-c*side**2).exp()/(2*c*side)


def near_tail_bounds(side=arb(4)):
    # The exact phase formula gives exp(lambda) exp(-(4/3)q^2) on the
    # central angular charts.  There are two signs of q and two saddles.
    gaussian = 4*LAMBDA.exp()*gaussian_one_side(arb(4)/3, side)
    delta = hull(arb(0), DELTA)
    v = hull(VMIN, arb(2))
    i1 = central.reduced_values(delta/v, v)[1]
    i0 = central.reduced_values(delta/v, v)[0]
    u = {}
    for order in (1, 3, 5):
        chain = generic_reduced_chain("I1", order)
        product = arb(i1.abs_upper())*arb(chain.abs_upper())/4
        weight = {1: 2/arb.pi(), 3: 1/(3*arb.pi()),
                  5: 1/(30*arb.pi())}[order]
        u[order] = gaussian*weight*product
    b = {}
    for order in (2, 4):
        chain = generic_reduced_chain("I0", order, arb(1)/2)
        product = arb(i0.abs_upper())*arb(chain.abs_upper())
        weight = {2: 1/arb.pi(), 4: 2/(3*arb.pi())}[order]
        b[order] = gaussian*weight*product
    return u, b


def crude_chain_constant(order, speed=arb(1)):
    # Taylor-composition majorant with |D_z^k I_n(z)|<=exp(|z|) and
    # |v^(j)|<=2 speed^j.  It bounds delta^order D^order after the
    # exponential has been removed.
    increment = [arb(0)]*(order+1)
    for j in range(1, order+1):
        increment[j] = DELTA**(j-1)*2*speed**j/factorial(j)
    powers = [[arb(0)]*(order+1) for _ in range(order+1)]
    powers[0][0] = arb(1)
    for k in range(1, order+1):
        powers[k] = central.jet_mul(powers[k-1], increment, order)
    coefficient = sum((powers[k][order]/factorial(k)
                       for k in range(order+1)), arb(0))
    return factorial(order)*coefficient


def far_scale():
    # On the exterior, sin(u)+|cos(u+eta)| <= 131/100+3/500=329/250.
    # Since sqrt(2)>707/500, the doubled phase gap is >49/250.
    gap = arb(49)/250
    return DELTA**(-arb(3)/2)*(-gap/DELTA).exp()


def far_tail_bounds():
    scale = far_scale()
    u = {
        1: scale*crude_chain_constant(1)/2,
        3: scale*crude_chain_constant(3)/12,
        5: scale*crude_chain_constant(5)/120,
    }
    b = {
        2: scale*crude_chain_constant(2, arb(1)/2),
        4: scale*2*crude_chain_constant(4, arb(1)/2)/3,
    }
    return u, b


def main():
    ctx.prec = 140
    near_u, near_b = near_tail_bounds()
    far_u, far_b = far_tail_bounds()
    for order in (1, 3, 5):
        print("U", order, "near", near_u[order], "far", far_u[order],
              "total", near_u[order]+far_u[order])
    for order in (2, 4):
        print("B", order, "near", near_b[order], "far", far_b[order],
              "total", near_b[order]+far_b[order])
    print("FIVE-FAMILY TAIL BUDGET DESIGN ONLY; FREEZE/LEDGER REQUIRED")


if __name__ == "__main__":
    main()
