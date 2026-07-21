from __future__ import annotations

import sys
from pathlib import Path

from flint import arb
import pytest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import surface_remainder_delta0_series_cover_design as cover  # noqa: E402


def test_endpoint_margin_requires_strict_lower_endpoint() -> None:
    assert bool(arb("0.1").lower() > 0)
    assert not bool(arb("+/- 0.1").lower() > 0)


def test_endpoint_cover_driver_exposes_strict_predicate() -> None:
    # The registered late-edge box has a positive lower endpoint, even though
    # Arb's compact `str()` rendering hides the midpoint and prints a
    # symmetric hull.  The driver must return only after the lower endpoint
    # test succeeds.
    _, _, _, margin = cover.judge_box(
        cover.Fraction(149, 50), cover.Fraction(3, 1), grids=(96,)
    )
    assert margin.lower() > 0
