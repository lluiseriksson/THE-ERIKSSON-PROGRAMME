from fractions import Fraction
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import certify_surface_high_beta_g5_lambda4 as cert


def test_frozen_lambda4_unit_partition() -> None:
    assert cert.UNITS == tuple(
        (start, start + 10) for start in range(100, 200, 10)
    )
    assert cert.unit_map()["lambda_100_110"] == (100, 110)
    assert cert.unit_map()["lambda_190_200"] == (190, 200)


def test_lambda4_geometry() -> None:
    cert.verify_geometry()
    assert Fraction(9, 1000) * 4 / 2 < Fraction(3, 80)
