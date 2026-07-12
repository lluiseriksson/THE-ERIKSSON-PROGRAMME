from fractions import Fraction
import importlib.util
from pathlib import Path

from flint import arb, ctx
import mpmath as mp


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "integral_remainder",
    ROOT/"scripts"/"surface_bessel_integral_remainder.py",
)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_binomial_coefficients_and_gamma_bound():
    assert MOD.coefficient(Fraction(1, 2), 0) == 1
    assert MOD.coefficient(Fraction(1, 2), 1) == Fraction(-1, 2)
    assert MOD.coefficient(Fraction(1, 2), 2) == Fraction(-1, 8)
    assert MOD.coefficient(Fraction(3, 2), 2) == Fraction(3, 8)
    ctx.prec = 120
    for a in (Fraction(3, 2), Fraction(7, 2), Fraction(13, 2)):
        for z in (arb(20), arb(40)):
            assert MOD.upper_gamma_elementary(a, z) >= z.gamma_upper(MOD.aq(a))


def test_scaled_integral_remainders_contain_defining_functions():
    ctx.prec = 160
    for family in ("A", "B"):
        for value in (20, 40, 80):
            z = arb(value)
            assert MOD.scaled_enclosure(z, family, 4).contains(
                MOD.exact_scaled(z, family)
            )


def test_remainder_contracts_with_z():
    ctx.prec = 160
    for family in ("A", "B"):
        radii = [MOD.scaled_enclosure(arb(z), family, 4).rad()
                 for z in (20, 40, 80)]
        assert radii[1] < radii[0]
        assert radii[2] < radii[1]


def test_recurrence_derivatives_contain_independent_values():
    ctx.prec = 180
    mp.mp.dps = 70
    definitions = {
        "A": lambda z: mp.exp(-z)*mp.besseli(1, z)/z,
        "B": lambda z: mp.exp(-z)*mp.besseli(2, z)/z**2,
    }
    for family, function in definitions.items():
        for value in (20, 40, 80):
            enclosures = MOD.derivative_enclosures(arb(value), family, 4)
            for derivative_order, enclosure in enumerate(enclosures):
                expected = mp.diff(function, mp.mpf(value), derivative_order)
                assert enclosure.contains(arb(str(expected))), (
                    family, value, derivative_order, enclosure, expected
                )


def test_uniform_relative_half_line_enclosures():
    ctx.prec = 180
    common = 1/(arb(2)*arb.pi()).sqrt()
    for family, power in (("A", arb(3)/2), ("B", arb(5)/2)):
        constant = MOD.uniform_relative_constant(family, 4, 20)
        assert constant > 0
        for value in (20, 21, 40, 80, 160):
            z = arb(value)
            enclosed = common*z**(-power)*MOD.relative_enclosure(
                z, family, 4, 20)
            assert enclosed.contains(MOD.exact_scaled(z, family))


def test_ratio_companion_is_algebraic_and_uniform():
    ctx.prec = 180
    q = MOD.quotient_coefficients(4)
    assert q[:3] == [Fraction(1), Fraction(-3, 2), Fraction(3, 8)]
    constant = MOD.ratio_uniform_constant(4, 20)
    assert constant > 0
    for value in (20, 21, 40, 80, 160):
        z = arb(value)
        exact = z*MOD.exact_scaled(z, "B")/MOD.exact_scaled(z, "A")
        assert MOD.ratio_relative_enclosure(z, 4, 20).contains(exact)


def test_ratio_deficit_remainder_on_saddle_ball():
    ctx.prec = 180
    constant = MOD.ratio_deficit_remainder_constant(4, 20)
    for zs_value in (40, 80, 160):
        zs = arb(zs_value)
        for w_value in ("0", "0.1", "0.3", "0.5"):
            w = arb(w_value)
            z = zs*(1-w).sqrt()
            exact = (MOD.exact_scaled(z, "B")/MOD.exact_scaled(z, "A")
                     -MOD.exact_scaled(zs, "B")/MOD.exact_scaled(zs, "A"))
            explicit = MOD.ratio_deficit_explicit(zs, w, 4)
            error = constant/zs**6
            assert (explicit+error*arb("0 +/- 1")).contains(exact)
