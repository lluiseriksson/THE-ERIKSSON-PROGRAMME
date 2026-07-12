from fractions import Fraction

import surface_remainder_delta0_extension_cover as mod


def test_cover_configuration_is_fixed():
    assert mod.DELTA_MAX == Fraction(1, 250)
    assert mod.GRIDS == (96, 192, 384, 768, 1024)
    assert tuple(sorted(mod.GRIDS)) == mod.GRIDS
