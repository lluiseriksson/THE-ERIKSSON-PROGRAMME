import certify_surface_remainder_delta0_r4_extension as mod


def test_grid_map_is_exact_partition():
    assert [mod.grid_for(i) for i in range(158)] == [96]*151+[192]*7


def test_production_dependencies_include_driver_and_exact_r4():
    assert mod.DEPENDENCIES[0].endswith(
        "certify_surface_remainder_delta0_r4_extension.py")
    assert "scripts/surface_remainder_delta0_fourth_coefficient.py" \
        in mod.DEPENDENCIES
