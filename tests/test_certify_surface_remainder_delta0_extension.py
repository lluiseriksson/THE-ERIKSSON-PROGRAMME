import certify_surface_remainder_delta0_extension as mod


def test_grid_map_is_exact_partition():
    assert [mod.grid_for(i) for i in range(158)] == (
        [192]*45+[384]*91+[768]*16+[1024]*3+[1536]*2+[1024]
    )


def test_production_dependencies_include_driver():
    assert mod.DEPENDENCIES[0].endswith(
        "certify_surface_remainder_delta0_extension.py")
