import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_delta0_endpoint",
    ROOT/"scripts"/"validate_surface_remainder_delta0_endpoint_transcript.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_authoritative_k2_endpoint_transcript_validates():
    assert MOD.validate()["t_boxes"] == 158


def test_k2_endpoint_validator_rejects_nonpositive_margin(tmp_path):
    text = MOD.TRANSCRIPT.read_text(encoding="utf-8")
    damaged = text.replace("margin_lower=[0.4747114165",
                           "margin_lower=[-0.4747114165", 1)
    path = tmp_path/"damaged.txt"
    path.write_text(damaged, encoding="utf-8")
    with pytest.raises(AssertionError, match="nonpositive"):
        MOD.validate(path)
