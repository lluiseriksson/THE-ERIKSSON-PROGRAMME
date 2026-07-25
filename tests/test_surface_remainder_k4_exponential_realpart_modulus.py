from fractions import Fraction
import unittest

from flint import acb, arb, ctx

from surface_remainder_k4_exponential_realpart_modulus import (
    _exponent,
    disk_guard,
    exponent_real_upper,
    modulus_upper,
)


class RealPartModulusTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 140

    def test_disk_guard_and_negative_radius(self):
        amplitude = (arb(29) / 40).cos()
        self.assertGreater(
            disk_guard(Fraction(7, 100), Fraction(4), amplitude).lower(), 0
        )
        with self.assertRaises(ValueError):
            disk_guard(Fraction(1), Fraction(4), amplitude)

    def test_real_slice_exponent_is_nonpositive_at_saddle_points(self):
        t = arb(29) / 10
        delta = acb(arb(1) / 20, 0)
        for mirror in (False, True):
            value = _exponent(acb(delta.real, 0), acb(arb("0.2"), 0),
                              acb(arb("0.3"), 0), acb(arb("1.1"), 0),
                              t, mirror)
            self.assertLessEqual(value.real.upper(), 0)

    def test_small_cover_returns_finite_bound(self):
        value = exponent_real_upper(
            delta_splits=1, spatial_splits=1, phi_splits=2,
        )
        self.assertTrue(value.is_finite())
        self.assertTrue(modulus_upper(value).is_finite())

    def test_split_counts_are_positive(self):
        with self.assertRaises(ValueError):
            exponent_real_upper(delta_splits=0)


if __name__ == "__main__":
    unittest.main()
