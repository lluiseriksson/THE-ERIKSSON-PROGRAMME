import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import certify_surface_high_beta_lambda18_5_interior as cert


def test_frozen_lambda18_5_threshold() -> None:
    assert cert.LAMBDA0 == Fraction(18, 5)
    assert cert.X_SPLIT == Fraction(81, 2500)
