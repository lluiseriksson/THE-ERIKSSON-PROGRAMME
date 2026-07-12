from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import surface_remainder_s2_value_arb as s2  # noqa: E402


def test_main_square_geometry_uses_exact_registered_side() -> None:
    assert s2.SIDE.overlaps(s2.arb(6) / 5)


def test_direct_value_lane_is_finite() -> None:
    y, kd, _, _, _ = s2.main_y_point(dz1=1.5, dz2=0.8, prec=80)
    assert kd > 0
    assert y.is_finite()
