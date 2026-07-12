import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_fifth_head",
    ROOT/"scripts"/"validate_surface_remainder_delta0_fifth_coefficient_transcript.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_authoritative_fifth_head_transcript_validates():
    assert MOD.validate()["lf_sha256"] == \
        "77a4478bf8a5a4c5d8e18cca70bd303accd56587477bf807d83cef4c06faaf3c"


def test_fifth_head_validator_rejects_mutation(tmp_path):
    text = MOD.TRANSCRIPT.read_text(encoding="utf-8")
    path = tmp_path/"damaged.txt"
    path.write_text(text.replace("1300912", "1300913"), encoding="utf-8")
    with pytest.raises(AssertionError, match="coefficient"):
        MOD.validate(path)
