import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_fourth_head",
    ROOT/"scripts"/"validate_surface_remainder_delta0_fourth_coefficient_transcript.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_authoritative_fourth_head_transcript_validates():
    assert MOD.validate()["transcript_sha256"] == \
        "f17669e4e47ed6fe0ac3bb11b31ffaa0998a9730f297e23942fcac39c84dde05"


def test_fourth_head_validator_rejects_mutation(tmp_path):
    text = MOD.TRANSCRIPT.read_text(encoding="utf-8")
    damaged = text.replace("1464*c**4", "1465*c**4")
    path = tmp_path/"damaged.txt"
    path.write_text(damaged, encoding="utf-8")
    with pytest.raises(AssertionError, match="coefficient"):
        MOD.validate(path)
