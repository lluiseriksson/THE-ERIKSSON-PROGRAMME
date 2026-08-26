from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99Eq360ComplexRegionalLaplacian.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99Eq360ComplexRegionalLaplacianAudit.draft.lean"


def test_analytic_laplacian_is_constructed_and_not_a_hilbert_adjoint():
    text = SOURCE.read_text(encoding="utf-8")
    implementation = text.split(
        "noncomputable def cmp99Eq360ComplexRegionalLaplacian", 1
    )[1]
    assert "def cmp99Eq360ComplexRegionalLaplacian" in text
    assert "cmp99Eq360ComplexCovariantDifference" in text
    assert "positiveEdgeOfPhysicalBond" in text
    assert "SpecialLinearGroup" in text
    assert "ContinuousLinearMap.adjoint" not in implementation
    assert "Delta0 Delta1" not in text


def test_backward_transport_uses_the_same_physical_link_inverse():
    text = SOURCE.read_text(encoding="utf-8")
    assert "((x.1.shiftBack i, i) : PhysicalBond d N)" in text
    assert ")))⁻¹" in text
    assert "cmp99Eq360ComplexDirichletExtend" in text


def test_audit_covers_all_public_declarations():
    source = SOURCE.read_text(encoding="utf-8")
    audit = AUDIT.read_text(encoding="utf-8")
    names = [
        "cmp99Eq360ComplexDirichletExtend",
        "cmp99Eq360ComplexDirichletExtend_add",
        "cmp99Eq360ComplexDirichletExtend_smul",
        "cmp99Eq360ComplexCovariantDifference",
        "cmp99Eq360ComplexCovariantDifference_add",
        "cmp99Eq360ComplexCovariantDifference_smul",
        "cmp99Eq360ComplexRegionalLaplacian",
        "cmp99Eq360ComplexRegionalLaplacian_apply",
    ]
    for name in names:
        assert name in source
        assert f"#print axioms YangMills.RG.{name}" in audit
