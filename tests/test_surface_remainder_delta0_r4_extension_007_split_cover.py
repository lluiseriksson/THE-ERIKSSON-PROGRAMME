from fractions import Fraction

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_007_split_cover as cover


def test_split_cover_contract_is_fixed_and_exhaustive():
    assert len(list(regular.sealed.born_t_boxes())) == 158
    assert cover.PHYSICAL_INNER == Fraction(23, 20)
    assert cover.GRID_LADDER == (96, 192, 384)
    assert len(cover.base.CORE_BOXES) == 3
    assert len(cover.base.ANNULUS_BOXES) == 7
