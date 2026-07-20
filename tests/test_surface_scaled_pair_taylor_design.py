from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = (ROOT / "scripts" / "surface_scaled_pair_taylor_design.py").read_text(
    encoding="utf-8"
)
DOC = (ROOT / "docs" / "SURFACE-G2-PAIR-TAYLOR-DESIGN-20260720.md").read_text(
    encoding="utf-8"
)
REMAINDER = (ROOT / "scripts" /
             "surface_scaled_pair_taylor_remainder_design.py").read_text(
                 encoding="utf-8"
             )


def test_pair_taylor_design_is_not_presented_as_a_certificate():
    assert "SCOPE truncated Taylor only" in SOURCE
    assert "Taylor remainder" in SOURCE
    assert "cannot promote G2" in DOC


def test_pair_identity_and_minor_cancellation_are_recorded():
    assert "A_m B_n-A_n B_m" in DOC
    assert "scaled_coefficient_jets" in SOURCE
    assert "coefficient_tail_bound" in SOURCE


def test_remainder_probe_is_explicitly_nonpromoting():
    assert "Design-only" in REMAINDER
    assert "does not promote a gate" in REMAINDER
