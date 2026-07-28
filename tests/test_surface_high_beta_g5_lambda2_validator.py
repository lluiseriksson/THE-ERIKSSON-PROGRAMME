import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from scripts import validate_surface_high_beta_g5_lambda2 as validator


def test_validator_owns_the_frozen_unit_map():
    assert validator.cert.unit_map() == {
        "lambda_75_80": (75, 80),
        "lambda_80_85": (80, 85),
        "lambda_85_90": (85, 90),
        "lambda_90_95": (90, 95),
        "lambda_95_100": (95, 100),
    }


def test_committed_production_replay_union():
    result = validator.validate(
        validator.COMMITTED_PRODUCTION,
        validator.COMMITTED_REPLAY,
    )
    assert result["rows"] == 225
    assert result["head"] == "613ed42d840e1e4d554c053fe81ae6f0c2aea40a"
