import certify_surface_remainder_delta0_r4_extension_006 as mod

def test_006_grid_map():
    assert [mod.grid_for(i) for i in range(158)] == [96]*137+[192]*21

def test_006_dependencies_name_v3():
    assert "scripts/surface_remainder_delta0_outer_domain_v3.py" in mod.DEPENDENCIES
