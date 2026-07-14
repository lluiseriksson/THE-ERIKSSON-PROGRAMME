from fractions import Fraction

import validate_surface_remainder_delta0_r4_extension_009_design_checkpoints as validate


def test_frozen_design_union_is_adjacent_and_has_expected_repair():
    units = validate.expected_units()
    endpoint = list(validate.regular.sealed.born_t_boxes())[-1][1]
    assert len(units) == 161
    assert units[0].lo == 0
    assert units[-1].hi == endpoint
    assert all(left.hi == right.lo for left, right in zip(units, units[1:]))
    assert validate.PARENT_INDICES == tuple(range(155)) + (157,)
    assert validate.TAIL_UNITS == (
        (155, 1, 0),
        (155, 1, 1),
        (156, 1, 0),
        (156, 2, 2),
        (156, 2, 3),
    )


def test_frozen_design_union_replaces_tail_without_changing_endpoints():
    units = validate.expected_units()
    endpoint = list(validate.regular.sealed.born_t_boxes())[-1][1]
    repaired = [unit for unit in units if unit.lo >= Fraction(31, 10)]
    assert [(unit.lo, unit.hi) for unit in repaired] == [
        (Fraction(31, 10), Fraction(311, 100)),
        (Fraction(311, 100), Fraction(78, 25)),
        (Fraction(78, 25), Fraction(313, 100)),
        (Fraction(313, 100), Fraction(627, 200)),
        (Fraction(627, 200), Fraction(157, 50)),
        (Fraction(157, 50), endpoint),
    ]
    assert all(unit.grid == 384 for unit in repaired)
