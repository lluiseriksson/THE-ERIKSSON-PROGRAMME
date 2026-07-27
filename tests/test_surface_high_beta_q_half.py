import hashlib
from fractions import Fraction
from pathlib import Path

from scripts.certify_surface_high_beta_q_half import certify
from scripts.verify_surface_high_beta_q_half_algebra import verify


ROOT = Path(__file__).resolve().parents[1]


def test_exact_algebra():
    verify()


def test_certified_high_beta_q_half():
    result = certify()
    assert result["passed"]
    assert result["target"] == Fraction(19, 20)
    assert result["worst"].lower() > 0


def test_transcript_binds_executed_script():
    transcript = (
        ROOT / "scripts" / "surface_high_beta_q_half_transcript_20260727.txt"
    ).read_text(encoding="utf-8").splitlines()
    script = ROOT / "scripts" / "certify_surface_high_beta_q_half.py"
    digest = hashlib.sha256(script.read_bytes()).hexdigest()
    assert f"PROVENANCE script_sha256={digest}" in transcript
    assert transcript[-1].startswith("CERTIFIED: <Phi>-(19/20)<D>>0")
