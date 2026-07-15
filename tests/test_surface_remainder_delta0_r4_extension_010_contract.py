import surface_remainder_delta0_r4_extension_010_hybrid_contract as contract
import surface_remainder_delta0_outer_domain_v7 as outer


def test_tenth_birth_contract_is_adjacent_and_wedge_owned():
    units = contract.regular_units()
    assert len(units) == 158
    assert units[0].lo == 0
    assert units[-1].hi == contract.T_CUT
    assert all(left.hi == right.lo for left, right in zip(units, units[1:]))
    assert contract.edge_starts_no_later_than_cut()
    assert contract.ANNULUS_BOXES[-1][1] == contract.NEW_DELTA_MAX


def test_tenth_birth_witnesses_are_registered_on_existing_grid_map():
    by_index = {unit.index: unit.grid for unit in contract.regular_units()}
    assert all(by_index[index] == grid
               for index, grid in contract.WITNESSES)


def test_v7_outer_domain_accepts_tenth_birth_and_rejects_later_delta():
    from fractions import Fraction
    bounds = outer.annulus_derivative_bounds_box_to(
        Fraction(9, 1000), Fraction(1, 100))
    assert set(bounds) == {"kd", "kf", "hdd", "hdf"}
    try:
        outer.annulus_derivative_bounds_box_to(
            Fraction(1, 100), Fraction(11, 1000))
    except ValueError:
        pass
    else:
        raise AssertionError("v7 must reject delta beyond 1/100")


def test_v8_outer_domain_contract_reaches_one_over_eighty_only():
    import surface_remainder_delta0_outer_domain_v8 as outer
    from fractions import Fraction
    bounds = outer.annulus_derivative_bounds_box_to(
        Fraction(1, 100), Fraction(1, 80))
    assert set(bounds) == {"kd", "kf", "hdd", "hdf"}
    radius, moving = outer.direct_moving_band_value_coefficients_from(
        Fraction(1, 80), Fraction(1181, 1000))
    assert radius == Fraction(21, 2)
    assert all(value.is_finite() for value in moving.values())
    try:
        outer.annulus_derivative_bounds_box_to(
            Fraction(1, 80), Fraction(81, 6400))
    except ValueError:
        pass
    else:
        raise AssertionError("v8 must reject delta beyond 1/80")
