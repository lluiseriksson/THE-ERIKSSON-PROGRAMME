import surface_remainder_delta0_r4_extension_009_fixed_cover as cover


def test_009_fixed_grid_map_is_a_partition():
    assert [cover.grid_for(index) for index in range(158)] == (
        [384]*50+[192]*96+[384]*12)
    assert cover.GRID_RANGES == (
        (0, 49, 384), (50, 145, 192), (146, 157, 384))


def test_009_segments_are_frozen_and_adjacent():
    assert cover.SEGMENTS == (
        (0, 13), (13, 25), (25, 38), (38, 50),
        (50, 98), (98, 146), (146, 152), (152, 158))
    assert all(left[1] == right[0]
               for left, right in zip(cover.SEGMENTS, cover.SEGMENTS[1:]))
    assert cover.SEGMENTS[0][0] == 0
    assert cover.SEGMENTS[-1][1] == 158

