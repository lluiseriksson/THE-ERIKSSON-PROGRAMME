from pathlib import Path

import validate_surface_remainder_k4_endpoint_terminal as validator


def test_endpoint_transcript_is_scoped_and_reproducible():
    assert validator.TRANSCRIPT.exists()
    fractions = validator.validate()
    assert max(float(value) for value in fractions.values()) < 0.60
