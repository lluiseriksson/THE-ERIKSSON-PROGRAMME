from fractions import Fraction

import pytest

import surface_remainder_delta0_r4_extension_009_tail_bisection as tail


def test_tail_bisection_contract_is_frozen():
    assert tail.INDICES == (155, 156)
    assert tail.MAX_DEPTH == 2
    assert tail.GRID == 384
    assert tail.subbox(155, 1, 0) == (Fraction(31, 10), Fraction(311, 100))
    assert tail.subbox(155, 1, 1) == (Fraction(311, 100), Fraction(78, 25))
    assert tail.subbox(156, 1, 0) == (Fraction(78, 25), Fraction(313, 100))
    assert tail.subbox(156, 1, 1) == (Fraction(313, 100), Fraction(157, 50))


def test_tail_quarters_are_adjacent_and_cover_each_parent():
    for index in tail.INDICES:
        pieces = [tail.subbox(index, 2, part) for part in range(4)]
        parent = list(tail.regular.sealed.born_t_boxes())[index]
        assert pieces[0][0] == parent[0]
        assert pieces[-1][1] == parent[1]
        assert all(left[1] == right[0]
                   for left, right in zip(pieces, pieces[1:]))


def test_tail_bisection_rejects_unregistered_inputs():
    with pytest.raises(ValueError):
        tail.subbox(154, 1, 0)
    with pytest.raises(ValueError):
        tail.subbox(156, 3, 0)
    with pytest.raises(ValueError):
        tail.subbox(156, 1, 2)

