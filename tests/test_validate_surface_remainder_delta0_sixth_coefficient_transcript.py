import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_sixth_head",
    ROOT/"scripts"/"validate_surface_remainder_delta0_sixth_coefficient_transcript.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_authoritative_sixth_head_transcript_validates():
    result = MOD.validate()
    assert result["raw_sha256"] == \
        "27725eaac35f1b5d29c556cbb188dbda24311b2e930825de9cb6681d1eeeec9c"
    assert result["lf_sha256"] == \
        "ee5fb3edfda129a5c0177577032ac8f307418ae64ffe1088b5b4675a87cf5556"


def test_sixth_head_validator_rejects_mutation(tmp_path):
    text = MOD.TRANSCRIPT.read_text(encoding="utf-8")
    path = tmp_path/"damaged.txt"
    path.write_text(text.replace("2557408", "2557409"), encoding="utf-8")
    with pytest.raises(AssertionError, match="mismatch"):
        MOD.validate(path)
