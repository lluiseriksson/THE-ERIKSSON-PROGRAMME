from fractions import Fraction

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_008_cover as cover


def test_008_cover_contract_is_fixed_and_exhaustive():
    assert len(list(regular.sealed.born_t_boxes())) == 158
    assert cover.PHYSICAL_INNER == Fraction(1181, 1000)
    assert cover.GRID_LADDER == (96, 192, 384)
    assert len(cover.base.CORE_BOXES) == 4
    assert len(cover.base.ANNULUS_BOXES) == 8
