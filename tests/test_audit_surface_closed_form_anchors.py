"""Release-gate contracts for independent exact anchors."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_final_seal_invokes_closed_form_anchor_gate() -> None:
    seal = (
        ROOT/"scripts"/"audit_surface_final_seal.py"
    ).read_text(encoding="utf-8")
    assert "import audit_surface_closed_form_anchors" in seal
    assert "CLOSED_FORM_ANCHORS_PROVED" in seal


def test_anchor_gate_names_both_interval_independent_relays() -> None:
    audit = (
        ROOT/"scripts"/"audit_surface_closed_form_anchors.py"
    ).read_text(encoding="utf-8")
    assert "near_relay.verify()" in audit
    assert "far_relay.verify()" in audit
    assert "companion_zero.verify()" in audit
    assert "normalization.audit(ROOT)" in audit
