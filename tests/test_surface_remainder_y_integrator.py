from __future__ import annotations

import sys
from pathlib import Path

from flint import arb


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
