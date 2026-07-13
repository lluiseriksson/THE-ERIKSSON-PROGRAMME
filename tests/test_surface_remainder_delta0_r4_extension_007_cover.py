import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_007_cover as cover
import surface_remainder_delta0_r4_extension_007_probe as probe


def test_007_cover_contract_is_exhaustive_and_fixed():
    assert len(list(regular.sealed.born_t_boxes())) == 158
    assert cover.GRID_LADDER == (96, 192, 384)
    assert probe.DELTA_MAX.numerator == 7
    assert probe.DELTA_MAX.denominator == 1000
    assert len(probe.CORE_BOXES) == 3
    assert len(probe.ANNULUS_BOXES) == 7
