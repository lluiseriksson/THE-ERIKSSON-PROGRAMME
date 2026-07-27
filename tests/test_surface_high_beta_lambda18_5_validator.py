import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import validate_surface_high_beta_lambda18_5_interior as validator


def test_committed_lambda18_5_interior_pair() -> None:
    result = validator.validate()
    assert result["rho"] < 3 / 200
    assert result["adverse"] < 9 / 10
    assert result["margin"] > 0
