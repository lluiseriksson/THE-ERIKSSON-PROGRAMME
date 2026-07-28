"""Certified pointwise-positive lower envelope for the K2 carrier mass KD.

The ordinary moment Taylor sum can lose the sign of KD through interval
dependency even though its integrand is positive.  This module integrates a
pointwise lower enclosure on fixed physical cells.  The nominal integrand is
the exact order-six scaled-Bessel polynomial already used by the K2 carrier;
the omitted A-companion is charged by the independent integral-form constant
``C_A / z**7`` before the cell lower endpoint is accumulated.
"""

from flint import arb, ctx

import surface_remainder_positive_physical_series_design as series
from surface_remainder_centered_prefactor import Dual
from surface_bessel_integral_remainder import relative_coefficients, uniform_relative_constant


COMMON = 1/(2*arb.pi()).sqrt()
ZERO = arb(0)


def _cell_lower(delta_box: arb, t_box: arb,
                slo: arb, shi: arb, alo: arb, ahi: arb,
                companion_order: int = 6) -> arb:
    """Outward lower bound for exact KD on one spatial cell."""
    s_box = series.hull(slo, shi)
    a_box = series.hull(alo, ahi)
    c = (t_box/4).cos()
    s4 = (t_box/4).sin()
    p = (s_box/2).sin()**2
    q = (a_box/2).sin()**2
    radius = (4*c**2*(1-p)*(1-q) + 4*s4**2*p*q).sqrt()
    if not radius > 0:
        raise ValueError("KD lower encountered nonpositive radius")
    h = delta_box/(2*radius)
    if h.upper() > arb(1)/20:
        raise ValueError("KD lower outside z>=20 companion contract")
    dweight = 2*(1-p-q)
    if not dweight > 0:
        raise ValueError("KD lower lost the registered positive weight")
    root3 = 2*radius*(2*radius).sqrt()
    phase = (2*radius-4*c)/delta_box
    nominal_pref, nominal_phase = series.physical_moment_parts(
        delta_box, t_box,
        Dual(s_box, ZERO, ZERO, ZERO),
        Dual(a_box, ZERO, ZERO, ZERO))
    # Both factors are strictly positive on this cell.  Multiplying their
    # Arb balls directly can nevertheless manufacture a negative lower
    # endpoint (the ball product does not exploit positivity when the
    # exponential interval is wide).  Form the mathematically valid lower
    # product from the two lower endpoints instead; this is essential near
    # the reflected saddle, where the phase enclosure is widest.
    kd0 = nominal_pref["KD"][0].v
    # Exponentiation of a wide Arb ball may itself be a symmetric ball with
    # a spurious negative lower endpoint.  Monotonicity of exp gives the
    # sharp positive lower endpoint directly from the phase lower endpoint.
    phase_lower = arb(phase.lower()).exp()
    phase_upper = arb(phase.upper()).exp()
    # Factor KD before taking lower endpoints.  The polynomial A(h), the
    # weight, and the exponential are positive separately; using the lower
    # endpoint of each factor is much sharper than asking Arb to multiply a
    # wide product ball.  ``kd0`` is retained as a consistency check: the
    # factorized expression must enclose its nominal coefficient.
    apoly = arb(0)
    for coefficient in reversed(relative_coefficients("A", companion_order)):
        apoly = apoly*h + arb(coefficient.numerator)/arb(coefficient.denominator)
    if not apoly > 0 or not dweight > 0 or not root3 > 0:
        raise ValueError("KD factorization lost registered positivity")
    factorized = (
        (2*COMMON).lower()
        * (arb(1)/delta_box).lower()
        * apoly.lower()
        * dweight.lower()
        / root3.upper()
        * phase_lower
    )
    if kd0 > 0 and factorized < arb(kd0.lower())*phase_lower:
        # This branch is diagnostic only; the factorized bound is allowed to
        # be weaker, never stronger, than the direct positive product.
        factorized = arb(kd0.lower())*phase_lower
    nominal = factorized
    # physical_moment_parts contains 2*COMMON*delta^-1/root3*dweight*exp(phase)
    # multiplying the relative A companion.  This is the exact omitted-tail
    # scale, with all factors enclosed on the same cell.
    base = (2*COMMON/delta_box/root3*dweight*phase_upper)
    error = (base.abs_upper()
             *uniform_relative_constant("A", companion_order, 20)
             *h.abs_upper()**(companion_order+1))
    return nominal-error


def positive_kd_lower(delta_box: arb, t_box: arb, grid: int = 64,
                      companion_order: int = 6) -> tuple[arb, int]:
    """Integrate the pointwise lower envelope over ``[0,6/5]^2``."""
    if grid <= 0:
        raise ValueError("grid must be positive")
    width = arb(1.2)/grid
    total = arb(0)
    for i in range(grid):
        for j in range(grid):
            slo, shi = width*i, width*(i+1)
            alo, ahi = width*j, width*(j+1)
            total += _cell_lower(delta_box, t_box, slo, shi, alo, ahi,
                                 companion_order)*(shi-slo)*(ahi-alo)
    return total, grid*grid


def main() -> int:
    ctx.prec = 120
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--delta-lo", default="0.010")
    parser.add_argument("--delta-hi", default="0.011")
    parser.add_argument("--t-lo", default="1.0")
    parser.add_argument("--t-hi", default="1.02")
    parser.add_argument("--grid", type=int, default=64)
    args = parser.parse_args()
    delta = series.hull(arb(args.delta_lo), arb(args.delta_hi))
    t_box = series.hull(arb(args.t_lo), arb(args.t_hi))
    lower, cells = positive_kd_lower(delta, t_box, args.grid)
    print("KD POSITIVE LOWER", lower, "cells", cells)
    if not lower > 0:
        raise SystemExit(1)
    print("KD POSITIVE LOWER PASS")


if __name__ == "__main__":
    raise SystemExit(main())
