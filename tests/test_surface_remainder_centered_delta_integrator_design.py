from flint import arb

from surface_remainder_centered_delta_integrator_design import (
    DELTA_FINAL,
    taylor_weight,
)


def test_taylor_weight_keeps_positive_width_on_narrow_box():
    # A box wholly below the terminal delta has a positive signed weight.
    lo = arb("0.0660")
    hi = arb("0.0661")
    weight = taylor_weight(lo, hi)
    expected = (hi - lo) * (DELTA_FINAL - (hi + lo) / 2)
    assert weight > 0
    assert expected > 0
    assert weight.overlaps(expected)


def test_taylor_weight_is_zero_at_a_box_centred_on_endpoint():
    # This is mathematically correct cancellation, not a certificate: a
    # production union must never use this signed weight across the endpoint.
    lo = arb("0.06665")
    hi = arb("0.0666833333333333")
    weight = taylor_weight(lo, hi)
    assert weight.lower() <= 0 <= weight.upper()
