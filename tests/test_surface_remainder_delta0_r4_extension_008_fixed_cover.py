import surface_remainder_delta0_r4_extension_008_fixed_cover as cover


def test_008_fixed_grid_map_is_a_partition():
    assert [cover.grid_for(index) for index in range(158)] == (
        [384]*50+[192]*96+[384]*12)
    assert cover.GRID_RANGES == (
        (0, 49, 384), (50, 145, 192), (146, 157, 384))
