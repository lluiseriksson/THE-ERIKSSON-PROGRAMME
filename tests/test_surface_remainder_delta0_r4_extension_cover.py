import surface_remainder_delta0_r4_extension_cover as cover


def test_r4_cover_ladder_is_fixed_and_monotone():
    assert cover.GRID_LADDER == (24, 48, 96, 192, 384)
    assert all(a < b for a, b in zip(
        cover.GRID_LADDER, cover.GRID_LADDER[1:]))


def test_unresolved_first_grid_does_not_change_the_registered_ladder():
    # The executable contract keeps every predetermined attempt; a failed
    # denominator enclosure is not permission to insert a new resolution.
    assert cover.GRID_LADDER[0] == 24
    assert cover.GRID_LADDER[-1] == 384
