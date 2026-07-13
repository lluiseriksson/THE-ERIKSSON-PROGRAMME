from fractions import Fraction

import surface_remainder_delta0_r4_extension_006_cover as cover


def test_006_cover_contract_is_fixed():
    assert cover.DELTA_DERIVATIVE_BOXES == (
        (Fraction(0), Fraction(1, 200)),
        (Fraction(1, 200), Fraction(3, 500)),
    )
    assert cover.PHYSICAL_INNER == Fraction(11, 10)
    assert cover.GRID_LADDER == (96, 192, 384)
