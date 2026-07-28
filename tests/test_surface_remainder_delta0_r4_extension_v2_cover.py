import surface_remainder_delta0_r4_extension_v2_cover as cover


def test_corrected_cover_ladder_is_fixed_and_monotone():
    assert cover.GRID_LADDER == (96, 192, 384)
    assert all(a < b for a, b in zip(
        cover.GRID_LADDER, cover.GRID_LADDER[1:]))
