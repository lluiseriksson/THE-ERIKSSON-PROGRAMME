"""Exact coordinate-transport identities for the K4 regular chart.

For one monomial ``delta^a sigma^b tau^c``, this module compares two
representations of the second derivative at fixed physical coordinates
``s=sqrt(delta)sigma`` and ``alpha=sqrt(delta)tau``.  It contains no
numerical K4 claim; it is an executable guard against omitting the Euler
transport terms in a future regular-ball implementation.
"""

from fractions import Fraction


def physical_second_coefficient(a: int, b: int, c: int) -> Fraction:
    """Coefficient after substituting scaled variables at fixed ``s,alpha``."""
    exponent = Fraction(a) - Fraction(b+c, 2)
    return exponent*(exponent-1)


def transported_second_coefficient(a: int, b: int, c: int) -> Fraction:
    """Coefficient from ``D^2-delta^-1 ED+(E+E^2/2)/(2 delta^2)``."""
    degree = Fraction(b+c)
    return (Fraction(a*(a-1)) - Fraction(a)*degree
            + degree/2 + degree**2/4)


def integrated_mass_second_coefficients(a: int):
    """Terms in ``(delta J)'' = 2 J' + delta J''`` for ``J=delta^a``."""
    direct = Fraction((a+1)*a)
    chart = Fraction(2*a+a*(a-1))
    return direct, chart
