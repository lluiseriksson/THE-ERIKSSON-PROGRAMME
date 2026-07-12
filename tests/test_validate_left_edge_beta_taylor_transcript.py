import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_left", ROOT/"scripts"/"validate_left_edge_beta_taylor_transcript.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_authoritative_left_edge_transcript_validates():
    result = MOD.validate()
    assert result["beta_boxes"] == 170
    assert result["normalized_boxes"] == 170
    assert result["regular_boxes"] == 883


def test_left_edge_validator_rejects_a_gap(tmp_path):
    text = MOD.TRANSCRIPT.read_text(encoding="utf-8")
    damaged = text.replace("beta-box [8.0,8.1]", "beta-box [8.0,8.05]")
    path = tmp_path/"damaged.txt"
    path.write_text(damaged, encoding="utf-8")
    with pytest.raises(AssertionError, match="gap"):
        MOD.validate(path)
