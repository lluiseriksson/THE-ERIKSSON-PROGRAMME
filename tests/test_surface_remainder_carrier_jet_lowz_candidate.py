from flint import arb

from surface_remainder_arb_jet2 import Jet2
import surface_remainder_carrier_jet_lowz_candidate as candidate


def test_lowz_adapter_uses_entire_series_inside_closed_box():
    z = Jet2(arb("1 +/- 0.01"), arb(1), arb(0))
    candidate.LOWZ_CALLS["A"] = candidate.FALLBACK_CALLS["A"] = 0
    out = candidate.a_scaled_jet(z)
    assert out.c0.is_finite()
    assert candidate.LOWZ_CALLS["A"] == 1
    assert candidate.FALLBACK_CALLS["A"] == 0


def test_crossing_four_rejects_lowz_branch():
    z = Jet2(arb("4 +/- 0.1"), arb(1), arb(0))
    candidate.LOWZ_CALLS["B"] = candidate.FALLBACK_CALLS["B"] = 0
    out = candidate.b_scaled_jet(z)
    assert out.c0.is_finite()
    assert candidate.LOWZ_CALLS["B"] == 0
    assert candidate.FALLBACK_CALLS["B"] == 1
