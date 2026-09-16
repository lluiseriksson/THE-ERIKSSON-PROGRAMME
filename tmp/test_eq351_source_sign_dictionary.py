"""Fail-closed checks for the CMP99 (3.3)/(3.8) sign dictionary."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp/BalabanCMP99Eq351PhysicalComplexCovariantDivergence.draft.lean"
AUDIT = ROOT / "tmp/BalabanCMP99Eq351PhysicalComplexCovariantDivergenceAudit.draft.lean"
DESIGN = ROOT / "tmp/EQ360-EQ351-EQ354-SOURCE-BOUND-DESIGN.md"


def test_source_derivative_is_the_named_negative_repository_difference() -> None:
    text = SOURCE.read_text(encoding="utf-8-sig")
    assert "def cmp99Eq351PhysicalComplexSourceCovariantDifference" in text
    assert (
        "theorem "
        "cmp99Eq351PhysicalComplexSourceCovariantDifference_eq_neg_repository"
        in text
    )
    assert "-cmp99Eq360ComplexCovariantDifference" in text
    assert "cmp99PhysicalGaugeBackgroundToSpecialLinear U" in text


def test_source_adjoint_keeps_negative_inverse_spacing_visible() -> None:
    text = SOURCE.read_text(encoding="utf-8-sig")
    assert "def cmp99Eq351PhysicalComplexSourceCovariantAdjoint" in text
    assert "(-((eta : ℂ)⁻¹)) • cmp99Eq351PhysicalComplexCovariantDivergence" in text
    assert (
        "cmp99Eq351PhysicalComplexSourceCovariantAdjoint_eq_smul_sum_oriented"
        in text
    )


def test_oriented_source_derivative_uses_oriented_endpoints() -> None:
    text = SOURCE.read_text(encoding="utf-8-sig")
    assert (
        "def cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference"
        in text
    )
    assert "(phi e.dstV) - phi e.srcV" in text
    assert (
        "cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference_neg"
        in text
    )
    assert "cmp99Eq351PhysicalComplexOrientedSource_transport" in text


def test_every_sign_dictionary_declaration_is_in_the_axiom_audit() -> None:
    text = AUDIT.read_text(encoding="utf-8-sig")
    declarations = (
        "cmp99Eq351PhysicalComplexSourceCovariantDifference",
        "cmp99Eq351PhysicalComplexSourceCovariantDifference_eq_neg_repository",
        "cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference",
        "cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference_pos",
        "cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference_neg",
        "cmp99Eq351PhysicalComplexOrientedSource_transport",
        "cmp99Eq351PhysicalComplexSourceCovariantAdjoint",
        "cmp99Eq351PhysicalComplexSourceCovariantAdjoint_apply",
        "cmp99Eq351PhysicalComplexSourceCovariantAdjoint_eq_smul_sum_oriented",
    )
    for declaration in declarations:
        assert f"#print axioms YangMills.RG.{declaration}" in text


def test_design_rejects_unscaled_divergence_as_printed_adjoint() -> None:
    text = DESIGN.read_text(encoding="utf-8-sig")
    assert "The derivative sign dictionary is portante" in text
    assert "would lose both a sign and a spacing factor" in text
    assert "may not be replaced by the unscaled divergence" in text
    assert "The oriented endpoint dictionary is a separate gate" in text
    assert "source-dictionary no-go" in text
    assert "appears to\ngive the opposite diagonal sign" in text
    assert "a standalone matrix-level lemma" in text
