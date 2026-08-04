"""Static contracts for the preregistered weak-main G2 composition."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT/"scripts"/"audit_surface_g2_weak_terminal_cover.py"


def test_weak_g2_audit_excludes_superseded_sharp_route() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    assert "validate_surface_remainder_delta0_r4_extension" not in source
    assert "verify_surface_high_beta_main_positive" not in source
    assert "weak_transcripts.validate(\"near\")" in source
    assert "weak_transcripts.validate(\"far\")" in source


def test_weak_g2_audit_requires_both_exact_relays_and_seam() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    assert "near_relay.verify()" in source
    assert "far_relay.verify()" in source
    assert 'far["t_max"] == near["t_min"] == Fraction(21, 10)' in source
    assert "G2_WEAK_TERMINAL_COVER_PROVED" in source
