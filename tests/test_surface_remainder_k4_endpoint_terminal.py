from pathlib import Path

import pytest
import validate_surface_remainder_k4_endpoint_terminal as validator


def test_endpoint_transcript_is_scoped_but_rejected_after_dependency_drift():
    assert validator.TRANSCRIPT.exists()
    lines = validator.TRANSCRIPT.read_text(encoding="utf-8").splitlines()
    assert "SCOPE one positive delta box only; no K4 union or theorem claim" in lines
    with pytest.raises(AssertionError, match="dependency content drift"):
        validator.validate()
