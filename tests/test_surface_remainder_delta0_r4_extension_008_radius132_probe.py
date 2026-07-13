from fractions import Fraction

import surface_remainder_delta0_r4_extension_008_radius132_probe as probe


def test_radius132_split_is_fixed_before_execution():
    assert probe.PHYSICAL_INNER == Fraction(1181, 1000)
    assert probe.base.BOX_INDICES == (0, 157)
    assert probe.base.GRID == 384
