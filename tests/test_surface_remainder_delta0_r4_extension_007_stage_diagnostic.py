import surface_remainder_delta0_r4_extension_007_stage_diagnostic as diagnostic
import surface_remainder_delta0_r4_extension_007_probe as probe


def test_stage_diagnostic_uses_registered_frontier():
    assert diagnostic.probe is probe
    assert len(probe.CORE_BOXES) == 3
    assert len(probe.ANNULUS_BOXES) == 7
    assert probe.GRIDS == (96, 192, 384)
