from fractions import Fraction

import surface_remainder_positive_birth008_witness_probe as probe


def test_birth_and_grid_ladder_are_frozen():
    assert probe.DELTA_LO == Fraction(1, 125)
    assert probe.DELTA_HI == Fraction(9, 1000)
    assert probe.DELTA_CENTER == (probe.DELTA_LO+probe.DELTA_HI)/2
    assert probe.WITNESS_INDEX == 0
    assert probe.GRID_LADDER == ((24, 12), (24, 16), (32, 20), (32, 24))
    assert probe.WORKERS == 4
    assert all(center % probe.WORKERS == 0
               and auxiliary % probe.WORKERS == 0
               for center, auxiliary in probe.GRID_LADDER)
    assert [auxiliary for _, auxiliary in probe.GRID_LADDER] == [12, 16, 20, 24]
