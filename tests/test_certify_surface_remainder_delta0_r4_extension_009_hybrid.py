import certify_surface_remainder_delta0_r4_extension_009_hybrid as cert


def test_hybrid_production_units_are_frozen():
    units = cert.hybrid.regular_units()
    assert len(cert.unit_map()) == len(units) == 158
    assert tuple(cert.unit_map()) == tuple(unit.slug for unit in units)
    assert tuple(unit.grid for unit in units) == (
        (384,) * 50 + (192,) * 96 + (384,) * 12
    )


def test_hybrid_dependencies_include_new_rate_and_full_outer_chain():
    required = {
        "scripts/surface_remainder_delta0_r4_extension_009_hybrid_contract.py",
        "scripts/surface_remainder_delta0_band_gap_design.py",
        "scripts/surface_remainder_delta0_tlocal_band_design.py",
        "scripts/surface_remainder_delta0_outer_domain_v6.py",
        "scripts/surface_remainder_delta0_outer_domain_v5.py",
        "scripts/surface_remainder_delta0_outer_domain_v3.py",
        "scripts/surface_remainder_delta0_outer_domain_v2.py",
    }
    assert required <= set(cert.DEPENDENCIES)


def test_hybrid_production_geometry_is_not_full_t_claim():
    assert cert.hybrid.regular_units()[-1].hi == cert.hybrid.T_CUT
    assert cert.hybrid.T_CUT < cert.hybrid.pi_hi()
    assert cert.hybrid.edge_starts_no_later_than_cut()
