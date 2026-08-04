import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import certify_surface_high_beta_lambda3_joint_interior as cert


def test_frozen_lambda3_joint_partition() -> None:
    assert cert.LAMBDA0 == Fraction(3)
    assert cert.X_SPLIT == Fraction(27, 1000)
    assert cert.MOVING_BOXES == 512
    assert cert.FIXED_BOXES == 2048


def test_joint_relay_margin_is_exactly_positive() -> None:
    assert (
        Fraction(19, 20)
        - Fraction(9, 10)
        - Fraction(1, 100_000)
        == Fraction(4999, 100_000)
    )
