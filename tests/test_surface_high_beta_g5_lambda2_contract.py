import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from scripts import certify_surface_high_beta_g5_lambda2 as cert


def test_high_beta_g5_lambda2_partition_contract():
    assert cert.UNITS == (
        (75, 80), (80, 85), (85, 90), (90, 95), (95, 100)
    )
    assert set(cert.unit_map()) == {
        "lambda_75_80", "lambda_80_85", "lambda_85_90",
        "lambda_90_95", "lambda_95_100",
    }
    assert Fraction(9, 1000) * 2 / 2 < Fraction(1, 100)
