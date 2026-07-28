"""Exact moving-square calculus and positive Gaussian tail envelopes.

This module supplies only the geometry shared by a future delta-zero
completion certificate.  It does not supply carrier-specific derivative
constants and therefore cannot promote K2, K4, S1''', or S2'''.

For

    F(delta) = integral_[0,L(delta)]^2 g(delta,x,y) dx dy,
    L(delta) = a / sqrt(delta),

the first three derivatives are written in terms of exact volume, face,
edge-derivative, and corner functionals before any inequality is applied.
The separate Gaussian helpers then bound already differentiated terms of
the form C (1+r)^n exp(-lambda r^2).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from flint import arb


def aq(value: Fraction | int) -> arb:
    if isinstance(value, int):
        return arb(value)
    return arb(value.numerator) / value.denominator


@dataclass(frozen=True)
class MovingSquareCoefficients:
    """Coefficients of the exact differentiated moving-square identity."""

    volume: tuple[arb, ...]
    face: tuple[arb, ...]
    face_delta: tuple[arb, ...]
    face_delta2: tuple[arb, ...]
    edge: tuple[arb, ...]
    edge_delta: tuple[arb, ...]
    corner2: tuple[arb, ...]


def moving_square_coefficients(delta: arb, side: arb) -> MovingSquareCoefficients:
    """Return exact coefficients through order three.

    The functional names are:

    ``A_j``
        integral of ``partial_delta^j g`` over the moving square;
    ``B_j``
        sum of the two face integrals of ``partial_delta^j g``;
    ``C_j``
        sum of outward coordinate derivatives on the faces plus twice the
        corresponding corner value, after ``j`` delta derivatives;
    ``D_0``
        the two pure second-coordinate face derivatives plus three times
        the sum of the two first-coordinate derivatives at the corner.

    Thus

    ``F''' = A3 + 3L'B2 + 3L''B1 + L'''B0
             + 3(L')^2 C1 + 3L'L'' C0 + (L')^3 D0``.
    """

    if not arb(delta.lower()) > 0:
        raise ValueError("moving-square calculus requires delta>0")
    if not arb(side.lower()) > 0:
        raise ValueError("moving-square side constant must be positive")
    length = side / delta.sqrt()
    first = -length / (2 * delta)
    second = 3 * length / (4 * delta**2)
    third = -15 * length / (8 * delta**3)
    zero = arb(0)
    one = arb(1)
    return MovingSquareCoefficients(
        volume=(one, one, one, one),
        face=(zero, first, second, third),
        face_delta=(zero, zero, 2 * first, 3 * second),
        face_delta2=(zero, zero, zero, 3 * first),
        edge=(zero, zero, first**2, 3 * first * second),
        edge_delta=(zero, zero, zero, 3 * first**2),
        corner2=(zero, zero, zero, first**3),
    )


def _phase_coercivity(scale: arb, physical_side: arb) -> arb:
    half_side = physical_side / 2
    u = half_side.sin() ** 2
    margin = 1 - u / (2 * scale**2)
    if not arb(margin.lower()) > 0:
        raise ValueError("phase coercivity margin is not positive")
    sinc = half_side.sin() / half_side
    return 2 * scale * margin * sinc**2 / 4


def main_phase_coercivity(t: arb, physical_side: arb = arb("1.2")) -> arb:
    """Positive ``lambda`` with main ``phase <= -lambda*r^2``.

    On the main physical chart,

    ``p = sigma^2 sinc(sqrt(delta)*sigma/2)^2 / 4``

    and similarly for ``q``.  Since both physical coordinates lie in
    ``[0,physical_side]``, monotonicity of sinc on ``[0,physical_side/2]``
    and ``delta*p,delta*q <= u=sin(physical_side/2)^2`` give

    ``p*q/(p+q) <= u/(2*delta)``

    and hence

    ``w >= (1-u/(2*c^2)) * sinc(physical_side/2)^2 * r^2 / 4``.

    The exact phase is ``-4*c*w/(1+sqrt(1-delta*w))`` and the denominator
    is at most two.
    """

    if not arb(t.lower()) > 0:
        raise ValueError("t must be positive")
    c = (t / 4).cos()
    return _phase_coercivity(c, physical_side)


def mirror_phase_coercivity(t: arb, physical_side: arb = arb("1.2")) -> arb:
    """Positive ``lambda`` with mirror ``phase <= -lambda*r^2``."""

    if not arb(t.lower()) > 0:
        raise ValueError("t must be positive")
    s4 = (t / 4).sin()
    return _phase_coercivity(s4, physical_side)


def gaussian_quadrant_tail_even(
    rate: arb, radius: arb, even_power: int
) -> arb:
    """Bound the quadrant integral outside ``r>=radius``.

    Returns the exact closed-form enclosure of

    ``integral_{theta=0}^{pi/2} integral_radius^inf
       r^even_power exp(-rate*r^2) r dr dtheta``.
    """

    if even_power < 0 or even_power % 2:
        raise ValueError("Gaussian radial power must be nonnegative and even")
    if not arb(rate.lower()) > 0 or not arb(radius.lower()) > 0:
        raise ValueError("Gaussian rate and radius must be positive")
    order = even_power // 2
    x = rate * radius**2
    polynomial = arb(0)
    factorial = 1
    power = arb(1)
    for index in range(order + 1):
        if index:
            factorial *= index
            power *= x
        polynomial += power / factorial
    gamma_tail = arb(factorial) * (-x).exp() * polynomial
    return arb.pi() * gamma_tail / (4 * rate ** (order + 1))


def gaussian_quadrant_polynomial_tail(
    rate: arb, radius: arb, degree: int
) -> arb:
    """Bound ``integral (1+r)^degree exp(-rate*r^2)`` outside ``r>=R``."""

    if degree < 0:
        raise ValueError("polynomial degree must be nonnegative")
    if not arb(radius.lower()) >= 1:
        raise ValueError("polynomial tail reduction requires radius>=1")
    even_power = degree if degree % 2 == 0 else degree + 1
    return (
        arb(2) ** degree
        * gaussian_quadrant_tail_even(rate, radius, even_power)
    )


def gaussian_face_polynomial_bound(
    rate: arb, length: arb, degree: int
) -> arb:
    """Bound a full positive face integral at ``x=length``.

    The returned quantity bounds

    ``integral_0^inf (1+sqrt(length^2+y^2))^degree
       exp(-rate*(length^2+y^2)) dy``.
    """

    if degree < 0:
        raise ValueError("polynomial degree must be nonnegative")
    if not arb(rate.lower()) > 0 or not arb(length.lower()) >= 1:
        raise ValueError("face bound requires rate>0 and length>=1")
    gaussian0 = arb.pi().sqrt() / (2 * rate.sqrt())
    if degree == 0:
        return (-rate * length**2).exp() * gaussian0
    gaussian_n = (
        aq(Fraction(degree + 1, 2)).gamma()
        / (2 * rate ** aq(Fraction(degree + 1, 2)))
    )
    convexity = arb(2) ** (degree - 1)
    return (
        arb(2) ** degree
        * convexity
        * (-rate * length**2).exp()
        * (length**degree * gaussian0 + gaussian_n)
    )


def gaussian_corner_polynomial_bound(
    rate: arb, length: arb, degree: int
) -> arb:
    """Bound a corner term at ``(length,length)``."""

    if degree < 0:
        raise ValueError("polynomial degree must be nonnegative")
    if not arb(rate.lower()) > 0 or not arb(length.lower()) >= 1:
        raise ValueError("corner bound requires rate>0 and length>=1")
    return (
        (1 + arb(2).sqrt() * length) ** degree
        * (-2 * rate * length**2).exp()
    )


def check() -> None:
    rate = main_phase_coercivity(aq(Fraction(29, 10)))
    mirror_rate = mirror_phase_coercivity(aq(Fraction(29, 10)))
    assert rate.is_finite() and rate > 0
    assert mirror_rate.is_finite() and mirror_rate > 0
    assert gaussian_quadrant_polynomial_tail(rate, arb(30), 12) > 0
    assert gaussian_face_polynomial_bound(rate, arb(30), 12) > 0
    assert gaussian_corner_polynomial_bound(rate, arb(30), 12) > 0
    coefficients = moving_square_coefficients(arb("0.001"), arb("1.2"))
    assert coefficients.face[1] < 0 < coefficients.face[2]
    assert coefficients.face[3] < 0
    print("delta-zero moving-tail geometry finite; no theorem promotion")


if __name__ == "__main__":
    check()
