"""Order-four inverse-z backend for the prospective beta>=20 G5 lane.

On the actual |q|<=5/2 moving charts, the Bessel arguments stay above 8
even at delta=1/20.  The inverse-z integral companion therefore crosses
delta=0 without the wide finite-z interval that produced NaNs in the first
finite bridge experiment.  This module remains design-only.
"""

from flint import arb, ctx

import surface_right_edge_five_family_central_design as central
from surface_bessel_integral_remainder import relative_enclosure_invz
from surface_remainder_arb_jet2 import hull


Z0 = 8
VALUE_FLOOR = arb(25)/62
INVZ_CEILING = arb(31)/250
ACTIVE_INVZ_CEILING = INVZ_CEILING
ACTIVE_VALUE_FLOOR = VALUE_FLOOR


def intersect(value, lower, upper):
    """Intersect an Arb enclosure with a separately proved real interval."""
    lo = arb(value.lower())
    hi = arb(value.upper())
    if hi < lower or lo > upper:
        raise ValueError("interval contradicts the central-chart contract")
    if lo < lower:
        lo = lower
    if hi > upper:
        hi = upper
    return hull(lo, hi)


def inverse_z_reduced_values(invz, v):
    # The independent moving-chart audit proves these two intersections for
    # every call made by the beta>=20 central integrator.  Applying them here
    # restores information lost when the same delta box occurs repeatedly in
    # the trigonometric interval expression.
    v = intersect(v, ACTIVE_VALUE_FLOOR, arb(2))
    invz = intersect(invz, arb(0), ACTIVE_INVZ_CEILING)
    if arb(invz.upper()) <= arb(1)/20:
        # Do not keep paying the z>=8 remainder once the actual box proves
        # z>=20.  This is the same integral-form companion used by the
        # delta=0 half-line lane and is strictly a tightening.
        arel = central.relative_companion(invz, "A")
        brel = central.relative_companion(invz, "B")
    else:
        arel = relative_enclosure_invz(invz, "A", 4, Z0)
        brel = relative_enclosure_invz(invz, "B", 4, Z0)
    root = 1/((2*arb.pi()).sqrt()*v.sqrt())
    return root*(brel+2*invz*arel), root*arel


def symmetric_q_sum(evaluator, side, grid):
    """Integrate paired q and -q boxes using one shared positive interval."""
    if grid < 2 or grid % 2:
        raise ValueError("symmetric q grid must be positive and even")
    half = grid//2
    width = arb(side)/half
    total = arb(0)
    for index in range(half):
        q = hull(index*width, (index+1)*width)
        total += (evaluator(q)+evaluator(-q))*width
    return total


def install(delta_max=arb(1)/20):
    global ACTIVE_INVZ_CEILING, ACTIVE_VALUE_FLOOR
    if not delta_max > 0 or delta_max > arb(1)/20:
        raise ValueError("beta20 backend delta endpoint outside contract")
    # The independently audited moving-chart floor v>=25/62 converts a
    # local delta endpoint into a sharper inverse-z endpoint.  This restores
    # correlation lost when delta/v is first formed as an interval.
    endpoint = arb(delta_max.upper())
    angle = arb.pi()/4-arb(5)/2*endpoint.sqrt()-3*endpoint/8
    local_floor = 2*angle.sin()
    if not local_floor > VALUE_FLOOR:
        local_floor = VALUE_FLOOR
    ACTIVE_VALUE_FLOOR = local_floor
    local = endpoint/ACTIVE_VALUE_FLOOR
    ACTIVE_INVZ_CEILING = min(INVZ_CEILING, local)
    central.reduced_values = inverse_z_reduced_values
    central.q_sum = symmetric_q_sum


def main():
    ctx.prec = 140
    install()
    print("BETA20 INVERSE-Z BACKEND DESIGN READY; PARAMETER COVER REQUIRED")


if __name__ == "__main__":
    main()
