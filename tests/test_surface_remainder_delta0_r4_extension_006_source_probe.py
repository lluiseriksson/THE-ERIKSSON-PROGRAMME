import surface_remainder_delta0_r4_extension_006_source_probe as mod


def test_source_probe_uses_registered_candidate_and_fixed_grid_contract():
    assert mod.probe.DELTA_CANDIDATE.numerator == 3
    assert mod.probe.DELTA_CANDIDATE.denominator == 500
