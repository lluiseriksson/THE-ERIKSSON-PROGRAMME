"""Complex-delta zero-freeness on the nominal K2 fixed square.

This is a local analytic input for a possible Cauchy remainder.  It covers
only the regular geometry and finite relative-Bessel polynomials on
``[0,12]^2``; it does not cover the true companion remainder or the moving
exterior.
"""

from __future__ import annotations

from flint import arb, ctx

from surface_bessel_integral_remainder import relative_coefficients


RHO = arb(7)/1000
SIDE = arb(12)
CMIN = arb(2).sqrt()/2
TERMS = 5


def polynomial_deviation(family: str, h_abs: arb) -> arb:
    coefficients = relative_coefficients(family, TERMS-1)
    return sum(
        (
            arb(abs(coefficient.numerator))/coefficient.denominator
            * h_abs**order
            for order, coefficient in enumerate(coefficients[1:], start=1)
        ),
        arb(0),
    )


def bounds() -> dict[str, arb]:
    sine_argument = RHO.sqrt()*SIDE/2
    # |sin z| <= sinh(|z|), by the absolute Taylor series.
    p_abs = sine_argument.sinh()**2
    d_floor = 2*(1-2*p_abs)
    radicand_deviation = 2*p_abs+p_abs**2/CMIN**2
    root_modulus_floor = (1-radicand_deviation).sqrt()
    root_from_one = (
        radicand_deviation/(1+root_modulus_floor)
    )
    one_plus_root_floor = 2-root_from_one
    h_abs = RHO/(4*CMIN*root_modulus_floor)
    a_deviation = polynomial_deviation("A", h_abs)
    b_deviation = polynomial_deviation("B", h_abs)
    return {
        "sine_argument": sine_argument,
        "p_abs": p_abs,
        "d_floor": d_floor,
        "radicand_deviation": radicand_deviation,
        "root_modulus_floor": root_modulus_floor,
        "root_from_one": root_from_one,
        "one_plus_root_floor": one_plus_root_floor,
        "h_abs": h_abs,
        "a_polynomial_deviation": a_deviation,
        "b_polynomial_deviation": b_deviation,
        "a_polynomial_floor": 1-a_deviation,
        "b_polynomial_floor": 1-b_deviation,
    }


def main() -> int:
    ctx.prec = 180
    values = bounds()
    assert values["p_abs"] < arb("0.28")
    assert values["d_floor"] > arb("0.8")
    assert values["radicand_deviation"] < arb("0.75")
    assert values["root_modulus_floor"] > arb("0.5")
    assert values["one_plus_root_floor"] > arb("1.5")
    assert values["a_polynomial_floor"] > arb("0.99")
    assert values["b_polynomial_floor"] > arb("0.99")
    print("K2 FIXED-SQUARE COMPLEX GEOMETRY")
    print("rho", RHO.str(30), "side", SIDE.str(30))
    for name, value in values.items():
        print(name, value.str(30))
    print(
        "K2 FIXED-SQUARE COMPLEX ZERO-FREENESS CERTIFIED; "
        "TRUE COMPANION AND EXTERIOR OPEN"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
