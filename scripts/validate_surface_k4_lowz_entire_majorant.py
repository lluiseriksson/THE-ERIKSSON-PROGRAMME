"""Regression checks for the preregistered low-z K4 Bessel branch.

This is an independent consistency check, not a K4 promotion.  Values are
recomputed directly with Arb's Bessel implementation and compared with the
positive-series endpoint hull.  Derivative signs and endpoint order are also
checked through order five, as required by the complete-monotonicity lemma
used by the certificate.
"""

from flint import arb, ctx

from surface_bessel_entire_lowz import (
    _point_derivatives,
    entire_outer_derivatives,
)


def direct_value(z: arb, family: str) -> arb:
    if z == 0:
        return arb(1) / (2 if family == "A" else 8)
    if family == "A":
        return (-z).exp() * z.bessel_i(1) / z
    if family == "B":
        return (-z).exp() * z.bessel_i(2) / z**2
    raise ValueError(family)


def main() -> None:
    ctx.prec = 160
    points = (arb(0), arb("0.1"), arb(1), arb(2), arb(4))
    box = arb("2 +/- 1.9")
    for family in ("A", "B"):
        for z in points:
            enclosure = entire_outer_derivatives(z, family, order=4)
            assert all(item.is_finite() for item in enclosure)
            assert enclosure[0].contains(direct_value(z, family)), (
                family, z, enclosure[0], direct_value(z, family))
            # Independent point evaluation of the series branch, including
            # the fifth derivative needed to justify monotonicity of order 4.
            point = _point_derivatives(z, family, order=5, terms=32)
            assert all(item.is_finite() for item in point)
            for order, value in enumerate(point):
                if order % 2 == 0:
                    assert value.lower() > 0, (family, z, order, value)
                else:
                    assert value.upper() < 0, (family, z, order, value)
        interval = entire_outer_derivatives(box, family, order=4)
        for z in (arb("0.1"), arb(2), arb("3.9")):
            assert interval[0].contains(direct_value(z, family)), (
                family, z, interval[0], direct_value(z, family))
    print("K4 LOW-Z ENTIRE MAJORANT REGRESSION PASS")
    print("CANDIDATE ONLY; NO K4/G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
