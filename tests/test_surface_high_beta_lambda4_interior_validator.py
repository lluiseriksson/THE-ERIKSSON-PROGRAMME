import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import validate_surface_high_beta_lambda4_interior as validator


def test_committed_lambda4_interior_pair() -> None:
    result = validator.validate()
    assert result["rho"] < 1 / 100
    assert result["adverse"] < 3 / 4
    assert result["margin"] > 0
