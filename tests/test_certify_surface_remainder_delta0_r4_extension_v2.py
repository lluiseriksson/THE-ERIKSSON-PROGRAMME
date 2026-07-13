import certify_surface_remainder_delta0_r4_extension_v2 as mod


def test_v2_grid_map_is_exact_partition():
    assert [mod.grid_for(i) for i in range(158)] == [96]*150+[192]*8


def test_v2_production_hashes_outer_repair():
    assert mod.DEPENDENCIES[0].endswith(
        "certify_surface_remainder_delta0_r4_extension_v2.py")
    assert "scripts/surface_remainder_delta0_outer_domain_v2.py" \
        in mod.DEPENDENCIES
