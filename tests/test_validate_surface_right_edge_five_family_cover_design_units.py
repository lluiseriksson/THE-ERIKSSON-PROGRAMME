import validate_surface_right_edge_five_family_cover_design_units as validator


def test_design_unit_partition_is_exact():
    units = validator.launcher.units()
    assert units[0] == (0, 5) and units[-1] == (70, 75)
    assert [index for lo, hi in units for index in range(lo, hi)] == list(
        range(75))
