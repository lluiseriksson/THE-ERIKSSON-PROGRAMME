from fractions import Fraction

import surface_remainder_delta0_r4_extension_006_split_probe as mod


def test_delta_split_is_the_six_immutable_births():
    assert mod.DELTA_BOXES == tuple(
        (Fraction(j, 1000), Fraction(j+1, 1000)) for j in range(6))
    assert mod.GRID == 96
