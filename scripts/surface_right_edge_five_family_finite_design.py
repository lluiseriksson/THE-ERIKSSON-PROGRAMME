"""Finite-delta design backend for the five-family right-edge integrator.

Unlike the half-line backend, this lane never touches delta=0.  It evaluates
the convergent integral-form scaled Bessel enclosures at the finite argument
z=v/delta, allowing exploratory coverage below beta=125 without changing the
frozen half-line design scripts.
"""

from flint import arb, ctx

import surface_right_edge_five_family_central_design as central
from surface_bessel_integral_remainder import scaled_enclosure


def integral_reduced_values(invz, v):
    if not invz > 0 or not v > 0:
        raise ValueError("finite scaled-Bessel backend requires z,v>0")
    z = 1/invz
    delta = invz*v
    root_delta = delta.sqrt()
    a = scaled_enclosure(z, "A", order=4)  # exp(-z) I1(z)/z
    b = scaled_enclosure(z, "B", order=4)  # exp(-z) I2(z)/z^2
    i1 = z*a/root_delta
    i0 = (z**2*b+2*a)/root_delta
    return i0, i1


def install():
    central.reduced_values = integral_reduced_values


def main():
    ctx.prec = 140
    install()
    delta, lam = arb(1)/20, arb(1)
    values = central.central_families(
        delta, lam, side=arb(5)/2, qgrid=80, rgrid=16,
        thetagrid=4, phigrid=4)
    p0, h = central.assemble_h(delta, lam, values)
    print("FINITE FIVE-FAMILY CENTRAL beta 20 lambda 1")
    for name, value in zip(("U0", "U1", "U2", "B0", "B1"), values):
        print(name, value, "lower", value.lower())
    print("P0", p0, "lower", p0.lower(), "H", h, "lower", h.lower())
    print("FINITE FIVE-FAMILY DESIGN ONLY; COMPLEMENT NOT CHARGED")


if __name__ == "__main__":
    main()
