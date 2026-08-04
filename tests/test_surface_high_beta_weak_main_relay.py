"""Regression test for the exact relaxed high-beta relay."""

from fractions import Fraction
import sys
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1]/"scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import verify_surface_high_beta_weak_main_relay as relay


def test_weak_main_relay_has_strict_exact_margin() -> None:
    result = relay.verify()
    assert result["lower_margin"] > 0
    assert result["main_charge"] < Fraction(53, 1000)
    assert result["mirror_charge"] < Fraction(861, 1000)
