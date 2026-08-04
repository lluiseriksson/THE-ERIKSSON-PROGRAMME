from fractions import Fraction

import surface_remainder_delta0_r4_extension_007_physical_split_probe as probe


def test_physical_split_probe_contract_is_fixed_before_execution():
    assert probe.PHYSICAL_SPLITS == (Fraction(23, 20), Fraction(119, 100))
    assert probe.BOX_INDICES == (0, 157)
    assert probe.GRID == 384
