"""Rigorous local Taylor enclosures for the K4 Bessel gap ``4 < z < 20``.

The authoritative K4 carrier deliberately has separate entire-series and
large-z branches.  This module is an isolated replacement experiment: it
uses exact Arb evaluations at the midpoint and a Taylor remainder bounded by
the Poisson moment representation of ``exp(-z) I_n(z)``.  It never changes the
authoritative dispatcher or promotes K4.
"""

from __future__ import annotations

from math import comb, factorial

from flint import arb

from surface_remainder_arb_jet2 import hull


def _moment_bound(order: int, z_lower: arb) -> arb:
    """Simple outward bound for |(exp(-z) I_n(z))^(order)|.

    From the Poisson representation, ``1-cos(phi) <= phi^2/2`` and
    ``1-cos(phi) >= 2 phi^2/pi^2`` give the displayed closed Gaussian bound.
    The bound is uniform in the integer Bessel order n.  It is intentionally
    conservative; the Taylor radius supplies the small factor.
    """
    if order < 0 or not z_lower > 0:
        raise ValueError("moment bound requires positive z and nonnegative order")
    j = arb(order)
    gamma = (j + arb("0.5")).gamma()
    return (gamma / (2*arb.pi()*arb(2)**order)
            * (arb.pi()**2/(2*z_lower))**(j+arb("0.5")))


def _b_derivatives_at(z: arb, order: int, nu: int) -> list[arb]:
    """Derivatives through ``order`` of b_n(z)=exp(-z)I_n(z) at z."""
    if nu < 0 or order < 1:
        raise ValueError("nu must be nonnegative and order must be positive")
    values = [arb(0)]*(order+1)
    i_n = z.bessel_i(nu)
    i_prev = z.bessel_i(nu-1) if nu else z.bessel_i(1)
    i_next = z.bessel_i(nu+1)
    values[0] = (-z).exp()*i_n
    values[1] = (-z).exp()*((i_prev+i_next)/2-i_n)

    # b_n satisfies z^2 b''+(2z^2+z)b'+(z-nu^2)b=0.  Differentiate this
    # identity repeatedly; all coefficients are rational functions of z.
    def coeff_a(j: int) -> arb:
        if j == 0:
            return -2-1/z
        return (-1)**(j+1)*arb(factorial(j))/z**(j+1)

    def coeff_b(j: int) -> arb:
        return (arb(nu*nu)*(-1)**j*arb(factorial(j+1))/z**(j+2)
                -(-1)**j*arb(factorial(j))/z**(j+1))

    for k in range(order-1):
        value = arb(0)
        for j in range(k+1):
            value += arb(comb(k, j))*(
                coeff_a(j)*values[k-j+1] + coeff_b(j)*values[k-j])
        values[k+2] = value
    return values


def _normalized_derivatives_at(z: arb, family: str, order: int) -> list[arb]:
    """Derivatives of A=e^-z I_1/z or B=e^-z I_2/z^2 at a point."""
    if family == "A":
        nu, power = 1, 1
    elif family == "B":
        nu, power = 2, 2
    else:
        raise ValueError(family)
    base = _b_derivatives_at(z, order, nu)
    result = []
    for r in range(order+1):
        value = arb(0)
        for j in range(r+1):
            q = r-j
            rising = arb(1)
            for ell in range(q):
                rising *= power+ell
            value += arb(comb(r, j))*base[j]*(-1)**q*rising/z**(power+q)
        result.append(value)
    return result


def _normalized_derivative_bound(z_lower: arb, family: str, order: int) -> arb:
    """Absolute bound for the requested normalized derivative."""
    if family == "A":
        nu, power = 1, 1
    elif family == "B":
        nu, power = 2, 2
    else:
        raise ValueError(family)
    out = arb(0)
    for j in range(order+1):
        q = order-j
        rising = arb(1)
        for ell in range(q):
            rising *= power+ell
        out += arb(comb(order, j))*_moment_bound(j, z_lower)*rising/z_lower**(power+q)
    return out


def derivative_enclosures(z: arb, family: str, order: int = 4,
                          taylor_order: int = 8) -> list[arb]:
    """Enclose derivatives 0..order on a positive interval in 4<=z<=20.

    The endpoint values are included for adapter use: the recurrence and the
    moment envelope are regular there.  The authoritative carrier still
    rejects the whole gap; this inclusive endpoint convention belongs only to
    this isolated experiment and does not alter any production contract.
    """
    if not (z.lower() >= 4 and z.upper() <= 20):
        raise ValueError("gap Taylor enclosure requires 4<=z<=20")
    if order < 0 or taylor_order < order:
        raise ValueError("invalid derivative orders")
    midpoint = (arb(z.lower())+arb(z.upper()))/2
    radius = (arb(z.upper())-arb(z.lower()))/2
    point = _normalized_derivatives_at(midpoint, family, taylor_order)
    result = []
    for r in range(order+1):
        # Avoid powers of a ball containing zero: python-flint can return NaN
        # for ``(0 +/- r)**k``.  Bound each nonconstant Taylor term by its
        # absolute radius instead; this is wider but remains rigorous.
        value = point[r]
        for k in range(taylor_order-r+1):
            if k == 0:
                continue
            term_radius = (point[r+k].abs_upper()*radius**k
                           /arb(factorial(k)))
            value += arb(0, term_radius.upper())
        remainder_order = taylor_order+1
        remainder = (_normalized_derivative_bound(arb(z.lower()), family,
                                                   remainder_order)
                     *radius**(remainder_order-r)
                     /arb(factorial(remainder_order-r)))
        result.append(value + arb(0, remainder.upper()))
    return result


def check() -> None:
    """Smoke: point values and both interval endpoints must be enclosed."""
    from flint import ctx
    ctx.prec = 160
    for lo, hi in (("4.01", "4.02"), ("10", "10.1"), ("19.8", "19.9")):
        z = hull(arb(lo), arb(hi))
        for family, nu, power in (("A", 1, 1), ("B", 2, 2)):
            values = derivative_enclosures(z, family)
            assert all(v.is_finite() for v in values)
            for endpoint in (arb(lo), arb(hi)):
                exact = [
                    # The point helper is the same differential recurrence,
                    # but this assertion checks interval containment at both
                    # endpoints independently of the Taylor cell.
                    _normalized_derivatives_at(endpoint, family, 4)[r]
                    for r in range(5)
                ]
                assert all(values[r].contains(exact[r])
                           for r in range(5)), (lo, hi, family)
    print("K4 GAP TAYLOR SMOKE PASS; isolated module only")


if __name__ == "__main__":
    check()
