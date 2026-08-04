import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import validate_surface_high_beta_lambda3_joint_interior as validator


def test_committed_lambda3_joint_pair() -> None:
    result = validator.validate()
    assert result["rho"] < 1 / 25
    assert result["adverse"] < 9 / 10
    assert result["margin"] > 0
