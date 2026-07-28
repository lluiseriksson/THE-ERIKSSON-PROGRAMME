from fractions import Fraction

import surface_remainder_delta0_r4_extension_008_intermediate_split_probe as probe


def test_intermediate_splits_are_fixed_before_execution():
    assert probe.PHYSICAL_SPLITS == (
        Fraction(7, 6), Fraction(47, 40), Fraction(71, 60))
    assert probe.base.BOX_INDICES == (0, 157)
    assert probe.base.GRID == 384
