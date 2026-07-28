"""Exact contracts for the weak-main far-zone relay."""

from fractions import Fraction
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    ROOT/"scripts"/"verify_surface_high_beta_weak_main_far_relay.py"
)
SPEC = importlib.util.spec_from_file_location("far_relay", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def test_far_relay_margin_is_strict() -> None:
    result = MODULE.verify()
    assert result["lower_margin"] > Fraction(899, 1000)
    assert result["mirror_charge"] == Fraction(1, 10**30)
    assert result["rest_charge"] == Fraction(1, 100_000)
