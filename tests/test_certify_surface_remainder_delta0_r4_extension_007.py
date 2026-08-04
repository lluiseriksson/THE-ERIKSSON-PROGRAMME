import certify_surface_remainder_delta0_r4_extension_007 as mod


def test_007_grid_map():
    assert [mod.grid_for(i) for i in range(158)] == [96]*119+[192]*39


def test_007_dependencies_are_byte_separate_and_transitive():
    assert "scripts/surface_remainder_delta0_outer_domain_v4.py" in mod.DEPENDENCIES
    assert "scripts/surface_remainder_delta0_outer_domain_v3.py" in mod.DEPENDENCIES
    assert "scripts/surface_remainder_delta0_outer_domain_v2.py" in mod.DEPENDENCIES


def test_007_split_and_radius_contract():
    assert mod.cover.PHYSICAL_INNER == mod.cover.Fraction(23, 20)
