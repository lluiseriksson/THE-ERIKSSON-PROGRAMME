from fractions import Fraction

import surface_remainder_delta0_r4_extension_008_split_probe as probe


def test_008_probe_contract_is_fixed_before_execution():
    assert probe.DELTA_MAX == Fraction(1, 125)
    assert len(probe.CORE_BOXES) == 4
    assert len(probe.ANNULUS_BOXES) == 8
    assert probe.PHYSICAL_SPLITS == (Fraction(23, 20), Fraction(119, 100))
    assert probe.BOX_INDICES == (0, 157)
    assert probe.GRID == 384
