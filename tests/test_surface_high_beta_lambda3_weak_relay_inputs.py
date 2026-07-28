"""Regression test for the pure lambda-three weak-relay validator."""

import sys
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1]/"scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import validate_surface_high_beta_lambda3_weak_relay_inputs as validator


def test_lambda3_transcript_implies_tighter_weak_relay_bounds() -> None:
    result = validator.validate()
    assert result["rho_upper"] < validator.RHO_THRESHOLD
    assert result["adverse_upper"] < validator.ADVERSE_THRESHOLD
