import certify_surface_remainder_delta0_r4_extension_008 as cert


def test_008_production_map_and_segments_are_frozen():
    assert [cert.grid_for(index) for index in range(158)] == (
        [384]*50+[192]*96+[384]*12)
    assert cert.SEGMENTS == (
        (0, 13), (13, 25), (25, 38), (38, 50),
        (50, 98), (98, 146), (146, 152), (152, 158))


def test_008_dependencies_include_the_full_outer_chain():
    assert "scripts/surface_remainder_delta0_outer_domain_v5.py" in cert.DEPENDENCIES
    assert "scripts/surface_remainder_delta0_outer_domain_v3.py" in cert.DEPENDENCIES
    assert "scripts/surface_remainder_delta0_outer_domain_v2.py" in cert.DEPENDENCIES


def test_008_physical_contract():
    assert cert.cover.cover.PHYSICAL_INNER == cert.cover.cover.Fraction(1181, 1000)
