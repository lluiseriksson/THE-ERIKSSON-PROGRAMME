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


def test_corrected_endpoint_cover_rejects_the_historical_late_edge() -> None:
    # After the full-moment normalization repair, the historical grid-96
    # sufficient route no longer resolves this late-edge box.  Preserve the
    # obstruction instead of treating the superseded route as terminal.
    with pytest.raises(RuntimeError, match="unresolved endpoint series box"):
        cover.judge_box(
            cover.Fraction(149, 50), cover.Fraction(3, 1), grids=(96,)
        )
