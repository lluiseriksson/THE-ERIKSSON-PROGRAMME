from pathlib import Path

import validate_surface_right_edge_five_family_halfline_transcript as validator


def test_transcript_validator_contract_exists():
    assert len(validator.cert.UNITS) == 15
    assert validator.transcript_path(
        validator.cert.UNITS[0]).name.endswith("_transcript.txt")
    assert len(set(validator.cert.DEPENDENCIES)) == len(
        validator.cert.DEPENDENCIES)
    assert all(
        (validator.ROOT/Path(relative)).is_file()
        for relative in validator.cert.DEPENDENCIES
    )
