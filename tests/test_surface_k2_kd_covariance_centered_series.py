from __future__ import annotations

import sys
from pathlib import Path

from flint import arb, arb_series, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import probe_surface_k2_kd_covariance_centered_series as probe  # noqa: E402


def test_law_of_total_covariance_assembly_is_exact_for_one_cell() -> None:
    ctx.prec = 180
    mass = arb_series([arb(2), arb(0)], 2)
    mean_a = arb_series([arb(3), arb(5)], 2)
    mean_g = arb_series([arb(7), arb(11)], 2)
    covariance = arb_series([arb(13), arb(17)], 2)
    cell = {
        "weight": mass,
        "wa": mass*mean_a,
        "wg": mass*mean_g,
        "wag": mass*(covariance+mean_a*mean_g),
    }
    actual = probe.assemble([cell])
    expected = 4*covariance
    assert all(
        left.overlaps(right)
        for left, right in zip(actual.coeffs(), expected.coeffs())
    )


def test_centered_series_contract_is_fixed() -> None:
    assert probe.GRID_LIST == (12, 24)
    assert probe.COEFFICIENT3_RADIUS_TARGET == arb(1968)
