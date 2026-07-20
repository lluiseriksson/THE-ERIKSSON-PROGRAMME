"""Design-only lambda-slope enclosure for the right-edge five-family lane.

The central charts depend on ``lambda`` only through the rate
``r*lambda*theta*phi/2``.  Integrating by parts in the outermost smearing
variable gives the exact identity ``lambda F' = F_flat - F``.  ``F_flat``
pins that variable at one endpoint while retaining the polynomial weights.
This module implements the five pinned integrals and the resulting
derivative of the cancellation-free numerator.  It is deliberately not a
certificate: a production/replay contract and an independent audit are
still required.
"""

from flint import arb

import surface_right_edge_five_family_central_design as central


def _q(evaluator, side, grid):
    return central.q_sum(evaluator, side, grid)


def _u_flat(delta, lam, derivative, side, qgrid, rgrid, thetagrid, phigrid):
    total = arb(0)
    # Pin the outermost smearing variable.  The remaining polynomial weights
    # are exactly those in integrate_u_family.
    if derivative == 1:
        for sign in (-1, 1):
            rate = sign * lam / 2
            def evaluate(q):
                return sum((central.u_chart_integrand(
                    delta, lam, rate, q, derivative, mirror)
                    for mirror in (False, True)), arb(0))
            total += _q(evaluate, side, qgrid)
        return -total / arb.pi()
    theta_count = thetagrid if derivative >= 3 else 1
    phi_count = phigrid if derivative >= 5 else 1
    for ri in range(rgrid):
        rlo = -arb(1) + 2*arb(ri)/rgrid
        rhi = -arb(1) + 2*arb(ri+1)/rgrid
        r = central.hull(rlo, rhi)
        if derivative == 3:
            theta_values = [(arb(1), arb(1), arb(1))]
        else:
            theta_values = []
            for ti in range(theta_count):
                tlo, thi = arb(ti)/theta_count, arb(ti+1)/theta_count
                theta_values.append((central.hull(tlo, thi), thi-tlo,
                                     central.integral_power(tlo, thi, 2)))
        for theta, theta_width, theta_weight in theta_values:
            rate = r * lam / 2 * theta
            if derivative == 3:
                factor = central.integral_power(rlo, rhi, 2)
            else:
                factor = (central.integral_power(rlo, rhi, 4)
                          * theta_weight)
            def evaluate(q):
                return sum((central.u_chart_integrand(
                    delta, lam, rate, q, derivative, mirror)
                    for mirror in (False, True)), arb(0))
            total += factor * _q(evaluate, side, qgrid)
    coefficient = {3: -1/(2*arb.pi()), 5: -1/(4*arb.pi())}[derivative]
    return coefficient * total


def _b_flat(delta, lam, derivative, side, qgrid, rgrid, thetagrid):
    total = arb(0)
    if derivative == 2:
        r = arb(1)
        rate = lam / 2
        def evaluate(q):
            return sum((central.b_chart_integrand(
                delta, rate, q, derivative, mirror)
                for mirror in (False, True)), arb(0))
        total = _q(evaluate, side, qgrid)
        return total / arb.pi()
    for ri in range(rgrid):
        rlo, rhi = arb(ri)/rgrid, arb(ri+1)/rgrid
        r = central.hull(rlo, rhi)
        rate = r * lam / 2
        factor = central.integral_power(rlo, rhi, 2)
        def evaluate(q):
            return sum((central.b_chart_integrand(
                delta, rate, q, derivative, mirror)
                for mirror in (False, True)), arb(0))
        total += factor * _q(evaluate, side, qgrid)
    return 2 * total / arb.pi()


def family_slopes(delta, lam, *, side=arb(5)/2, qgrid=40, rgrid=8,
                  thetagrid=4, phigrid=4):
    """Return the five exact lambda derivatives, as design enclosures."""
    values = central.central_families(
        delta, lam, side=side, qgrid=qgrid, rgrid=rgrid,
        thetagrid=thetagrid, phigrid=phigrid)
    flats = (
        _u_flat(delta, lam, 1, side, qgrid, rgrid, thetagrid, phigrid),
        _u_flat(delta, lam, 3, side, qgrid, rgrid, thetagrid, phigrid),
        _u_flat(delta, lam, 5, side, qgrid, rgrid, thetagrid, phigrid),
        _b_flat(delta, lam, 2, side, qgrid, rgrid, thetagrid),
        _b_flat(delta, lam, 4, side, qgrid, rgrid, thetagrid),
    )
    return values, tuple((flat - value) / lam
                         for flat, value in zip(flats, values))


def _series_derivative(y, family, terms=8):
    from fractions import Fraction
    from math import factorial
    if family == "syy":
        coeff = lambda n: Fraction((-1)**n*(n+1)*(n+2), factorial(2*n+5))
    elif family == "jyy":
        coeff = lambda n: Fraction((-1)**n*2*(n+2)*(n+3), factorial(2*n+7))
    else:
        raise ValueError(family)
    total = arb(0)
    for n in reversed(range(terms)):
        c = coeff(n)
        total = total*y + arb(c.numerator)/c.denominator
    c = abs(coeff(terms))
    return total + 2*arb(c.numerator)/c.denominator * arb(y.abs_upper())**terms * arb("0 +/- 1")


def assemble_p0_slope(delta, lam, families, slopes):
    """Cancellation-free P0 and its lambda derivative (design only)."""
    U0, U1, U2, B0, B1 = families
    dU0, dU1, dU2, dB0, dB1 = slopes
    y = (delta*lam/2)**2
    s = central.elementary_series(y, "s")
    sy = central.elementary_series(y, "sy")
    j = central.elementary_series(y, "j")
    jy = central.elementary_series(y, "jy")
    syy, jyy = _series_derivative(y, "syy"), _series_derivative(y, "jyy")
    dy = delta**2 * lam / 2
    A0 = j*delta**2*U0 + 2*s*U1
    A1 = jy*delta**4*U0 + (j+2*sy)*delta**2*U1 + 2*s*U2
    A0p = (jy*dy)*delta**2*U0 + j*delta**2*dU0 + 2*(sy*dy)*U1 + 2*s*dU1
    A1p = (jyy*dy)*delta**4*U0 + jy*delta**4*dU0
    A1p += ((jy+2*syy)*dy)*delta**2*U1 + (j+2*sy)*delta**2*dU1
    A1p += 2*(sy*dy)*U2 + 2*s*dU2
    P0 = A0*B0 + lam**2*(A1*B0-A0*B1)/4
    P0p = A0p*B0 + A0*dB0 + lam*(A1*B0-A0*B1)/2
    P0p += lam**2*(A1p*B0+A1*dB0-A0p*B1-A0*dB1)/4
    return P0, P0p
