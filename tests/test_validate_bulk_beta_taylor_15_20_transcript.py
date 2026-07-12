import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_bulk_15_20",
    ROOT/"scripts"/"validate_bulk_beta_taylor_15_20_transcript.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_authoritative_extension_transcript_validates():
    result = MOD.validate()
    assert result["beta_boxes"] == 89
    assert result["t_boxes"] == 4736


def test_extension_validator_rejects_wrong_refinement(tmp_path):
    text = MOD.TRANSCRIPT.read_text(encoding="utf-8")
    damaged = text.replace("beta-box [16.1, 16.15]", "beta-box [16.1, 16.2]")
    path = tmp_path/"damaged.txt"
    path.write_text(damaged, encoding="utf-8")
    with pytest.raises(AssertionError, match="wrong step"):
        MOD.validate(path)
