from __future__ import annotations

import sys
from pathlib import Path

from flint import arb
import pytest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import surface_remainder_y_integrator as yi  # noqa: E402


def test_dual_integral_is_exact_for_affine_data() -> None:
    center = yi.Dual(arb(3), arb(2), arb(-1))
    box = yi.Dual(arb(3), arb(2), arb(-1))
    result = yi._dual_integral(center, box, arb(1), arb(2), arb(8))
    assert result == 24


def test_linear_exponential_moments_handle_zero_gradient() -> None:
    assert yi._linear_integral(arb(0), arb(3)) == 3
    assert yi._linear_first_moment(arb(0), arb(3)) == 0


def test_y_integrator_scaffold() -> None:
    yi.check()


def test_relative_priority_accepts_explicit_scales() -> None:
    scales = {
        (name, coefficient): 1.0
        for name in yi.RAW_NAMES
        for coefficient in ("c0", "c1", "c2")
    }
    totals, cells = yi.integrate_raw(
        arb(1) / 15, max_cells=64, relative_scales=scales
    )
    assert cells >= 64
    assert set(totals) == set(yi.RAW_NAMES)


def test_terminal_sensitivity_weights_are_finite() -> None:
    moments = {
        "KD": yi.Jet2(arb(3), arb(1), arb("0.2")),
        "KNc": yi.Jet2(arb("0.1"), arb("0.2"), arb("0.3")),
        "HDD": yi.Jet2(arb(2), arb("0.4"), arb("0.1")),
        "GNc": yi.Jet2(arb("0.2"), arb("0.3"), arb("0.4")),
    }
    weights = yi.terminal_sensitivity_weights(moments, arb(1) / 20)
    assert len(weights) == 12
    assert all(value >= 0 and value < float("inf") for value in weights.values())
    assert any(value > 0 for value in weights.values())
    value_weights = yi.terminal_sensitivity_weights(
        moments, arb(1) / 20, target="c0"
    )
    assert len(value_weights) == 12
    assert any(value > 0 for value in value_weights.values())


def test_linear_priority_accepts_terminal_weights() -> None:
    weights = {
        (name, coefficient): 1.0
        for name in yi.RAW_NAMES
        for coefficient in ("c0", "c1", "c2")
    }
    totals, cells = yi.integrate_raw(
        arb(1) / 15, max_cells=64, linear_weights=weights
    )
    assert cells >= 64
    assert set(totals) == set(yi.RAW_NAMES)


def test_t_jet_integrator_lane_is_finite() -> None:
    y, cells, _, weights = yi.sensitivity_centered_main_y_t(
        arb(1)/20, arb("2.9"), pilot_cells=64, max_cells=64
    )
    assert cells >= 64
    assert all(value.is_finite() for value in (y.c0, y.c1, y.c2))
    assert len(weights) == 12


def test_forced_subdivision_has_a_loud_depth_floor() -> None:
    def never_finite(*_args, **_kwargs):
        raise ValueError("synthetic box must subdivide")

    with pytest.raises(RuntimeError, match="reached depth 3"):
        yi.integrate_raw(
            arb(1)/20, max_cells=16, seed_grid=1,
            parts_function=never_finite, max_forced_depth=3,
        )


def test_scaled_fixed_square_lane_is_finite_at_threshold() -> None:
    y, cells, _ = yi.centered_scaled_fixed_square_y(
        arb(1)/20, pilot_cells=64, max_cells=64, beta1=20
    )
    assert cells >= 64
    assert all(value.is_finite() for value in (y.c0, y.c1, y.c2))
