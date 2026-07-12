import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_right",
    ROOT/"scripts"/"validate_right_edge_beta_taylor_transcript.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_authoritative_right_edge_transcript_union_validates():
    result = MOD.validate()
    assert result["beta_boxes"] >= 170
    assert result["normalized_boxes"] >= 170
    assert result["regular_boxes"] > 0
    assert len(result["transcript_sha256"]) == 6


def test_right_edge_validator_rejects_a_gap(tmp_path):
    specs = list(MOD.SPECS)
    source, start, end, step, git_head = specs[0]
    text = source.read_text(encoding="utf-8")
    text = text.replace("beta-box [8.0,8.1]", "beta-box [8.0,8.05]")
    damaged = tmp_path/"damaged.txt"
    damaged.write_text(text, encoding="utf-8")
    specs[0] = (damaged, start, end, step, git_head)
    with pytest.raises(AssertionError, match="gap"):
        MOD.validate(specs)
