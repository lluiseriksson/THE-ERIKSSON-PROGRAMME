from flint import ctx

from surface_remainder_delta0_derivative_tail import moment_majorants
from probe_surface_h_tail_cauchy_majorant import (
    RHO,
    cauchy_budget,
    finite_order_disk_majorants,
)


def test_budget_is_the_registered_endpoint_budget():
    ctx.prec = 180
    data = cauchy_budget()
    assert data["q"] > 0.9523 and data["q"] < 0.9524
    assert data["required_M"] > 0.0001679
    assert data["required_M"] < 0.0001680


def test_finite_order_probe_is_finite_and_raw_only():
    ctx.prec = 180
    values = finite_order_disk_majorants()
    assert RHO > 0
    assert set(values) == {"kd", "kf", "hdd", "hdf", "raw_bilinear"}
    assert all(value.is_finite() and value >= 0 for value in values.values())
    assert values["raw_bilinear"] > 0
    # The test intentionally does not assert a theorem-level Cauchy bound:
    # the omitted coefficient tail and denominator floor remain separate.
    assert len(moment_majorants()) == 4
