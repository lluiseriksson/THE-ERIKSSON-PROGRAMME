from fractions import Fraction

import pytest

import surface_remainder_delta0_outer_domain_v5 as v5
import surface_remainder_delta0_outer_domain_v6 as v6
import surface_remainder_delta0_r4_extension_009_split_probe as probe


def test_v6_extends_only_to_nine_thousandths():
    assert v6.MAX_DELTA == Fraction(9, 1000)
    v6._require_delta(Fraction(9, 1000))
    with pytest.raises(ValueError):
        v6._require_delta(Fraction(1, 100))


def test_v5_contract_remains_closed_at_eight_thousandths():
    assert v5.MAX_DELTA == Fraction(1, 125)
    with pytest.raises(ValueError):
        v5._require_delta(Fraction(9, 1000))


def test_probe_partition_and_witnesses_are_frozen():
    assert probe.DELTA_MAX == Fraction(9, 1000)
    assert probe.CORE_BOXES[0][0] == 0
    assert probe.CORE_BOXES[-1][1] == probe.DELTA_MAX
    assert all(left[1] == right[0]
               for left, right in zip(probe.CORE_BOXES, probe.CORE_BOXES[1:]))
    assert probe.ANNULUS_BOXES == tuple(
        (Fraction(j, 1000), Fraction(j + 1, 1000)) for j in range(9))
    assert probe.PHYSICAL_SPLITS == (
        Fraction(1181, 1000), Fraction(1183, 1000),
        Fraction(237, 200), Fraction(1187, 1000))
    assert probe.WITNESSES == ((0, 384), (50, 192), (157, 384))
