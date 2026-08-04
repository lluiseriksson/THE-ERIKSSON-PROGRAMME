from fractions import Fraction

import surface_remainder_delta0_r4_extension_009_hybrid_contract as hybrid


def test_hybrid_geometry_is_exact_and_frozen():
    assert hybrid.OLD_DELTA_MAX == Fraction(1, 125)
    assert hybrid.NEW_DELTA_MAX == Fraction(9, 1000)
    assert hybrid.CWIN == Fraction(3, 2)
    assert hybrid.T_CUT == Fraction(313, 100)
    assert hybrid.edge_starts_no_later_than_cut()
    assert hybrid.T_CUT - (
        hybrid.pi_hi() - hybrid.CWIN * hybrid.OLD_DELTA_MAX
    ) > 0


def test_hybrid_regular_units_cover_zero_to_cut_without_gaps():
    units = hybrid.regular_units()
    assert len(units) == 158
    assert units[0].lo == 0
    assert units[-1].hi == hybrid.T_CUT
    assert all(left.hi == right.lo for left, right in zip(units, units[1:]))
    assert hybrid.PARENT_INDICES == tuple(range(155))
    assert hybrid.TAIL_UNITS == (
        (155, 1, 0),
        (155, 1, 1),
        (156, 1, 0),
    )


def test_hybrid_cut_assigns_entire_complement_to_moving_edge():
    # For delta>=OLD_DELTA_MAX, pi-CWIN*delta is nonincreasing.
    for delta in (hybrid.OLD_DELTA_MAX, hybrid.NEW_DELTA_MAX):
        assert hybrid.pi_hi() - hybrid.CWIN * delta <= hybrid.T_CUT
