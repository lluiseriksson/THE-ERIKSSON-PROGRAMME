from fractions import Fraction

import surface_remainder_positive_birth008_witness_probe as probe


def test_birth_and_grid_ladder_are_frozen():
    assert probe.DELTA_LO == Fraction(1, 125)
    assert probe.DELTA_HI == Fraction(9, 1000)
    assert probe.DELTA_CENTER == (probe.DELTA_LO+probe.DELTA_HI)/2
    assert probe.WITNESS_INDEX == 0
    assert probe.GRID_LADDER == ((8, 2), (16, 4), (24, 6), (32, 8))
    assert probe.WORKERS == 4
