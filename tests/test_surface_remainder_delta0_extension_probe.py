from fractions import Fraction

from flint import arb

import surface_remainder_delta0_extension_probe as mod


def test_exact_fraction_conversion():
    assert mod.aq(Fraction(3, 1000)).overlaps(arb("0.003"))


def test_extension_module_does_not_mutate_sealed_lane():
    assert mod.sealed.DELTA_MAX == Fraction(1, 1000)
