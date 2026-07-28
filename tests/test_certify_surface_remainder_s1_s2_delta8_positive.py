from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import certify_surface_remainder_s1_s2_delta8_positive as campaign  # noqa: E402


def test_born_units_are_exact_positive_partition() -> None:
    assert len(campaign.UNITS) == 73
    assert campaign.UNITS[0] == (Fraction(61, 2000), Fraction(62, 2000))
    assert campaign.UNITS[-1] == (Fraction(133, 2000), Fraction(1, 15))
    assert all(lo > 0 and lo < hi for lo, hi in campaign.UNITS)
    assert all(
        campaign.UNITS[index][1] == campaign.UNITS[index + 1][0]
        for index in range(len(campaign.UNITS) - 1)
    )


def test_unit_names_and_grid_boundary() -> None:
    assert campaign.unit_name(0) == "u000"
    assert campaign.unit_name(72) == "u072"
    assert campaign.UNITS[17][0] < Fraction(79, 2000)
    assert campaign.UNITS[18][0] == Fraction(79, 2000)


def test_calibration_is_deterministic_and_continuous_at_knots() -> None:
    ctx.prec = 180
    first = campaign.calibration_at(Fraction(61, 2000))
    assert all(
        value.overlaps(arb(expected))
        for value, expected in zip(
            first, campaign.CALIBRATION_KNOTS[0][1]
        )
    )
    assert [value.str(80) for value in first] == [
        value.str(80)
        for value in campaign.calibration_at(Fraction(61, 2000))
    ]
    for knot, values in campaign.CALIBRATION_KNOTS:
        got = campaign.calibration_at(knot)
        assert all(
            value.overlaps(arb(expected))
            for value, expected in zip(got, values)
        )


def test_s2_fraction_is_positive_and_exactly_weighted() -> None:
    ctx.prec = 180
    lo, hi = campaign.aq(Fraction(61, 2000)), campaign.aq(Fraction(62, 2000))
    got = campaign.s2_fraction(arb(2), lo, hi)
    delta_final = campaign.aq(Fraction(1, 15))
    weight = delta_final * (hi - lo) - (hi**2 - lo**2) / 2
    theta3 = campaign.closed_forms(campaign.aq(Fraction(29, 10)))[3]
    expected = 60 * weight / (theta3 * delta_final)
    assert got.overlaps(expected)
    assert got > 0


def test_repository_dependency_list_contains_driver_and_exact_lanes() -> None:
    relative = {
        path.relative_to(ROOT).as_posix()
        for path in campaign.repository_dependencies()
    }
    assert "scripts/certify_surface_remainder_s1_s2_delta8_positive.py" in relative
    assert "scripts/surface_remainder_s1_delta8_exact.py" in relative
    assert "scripts/surface_remainder_s2_delta8_exact.py" in relative
