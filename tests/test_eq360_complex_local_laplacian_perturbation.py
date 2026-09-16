from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99Eq360ComplexLocalLaplacianPerturbation.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99Eq360ComplexLocalLaplacianPerturbationAudit.draft.lean"


def test_local_v1_is_constructed_from_two_stencils():
    text = SOURCE.read_text(encoding="utf-8")
    assert text.count("cmp99Eq360ComplexCovariantDifference U0") >= 2
    assert text.count("cmp99Eq360ComplexCovariantDifference U1") >= 2
    assert "U0 (positiveEdgeOfPhysicalBond" in text
    assert "U1 (positiveEdgeOfPhysicalBond" in text
    assert "cmp99Eq360ComplexDirichletExtend Omega phi" in text


def test_no_free_v1_or_bound_is_accepted():
    text = SOURCE.read_text(encoding="utf-8")
    signature = text.split(
        "noncomputable def cmp99Eq360ComplexLocalLaplacianPerturbation", 1
    )[1].split(":=", 1)[0]
    for forbidden in ("V1 :", "V :", "bound :", "hbound"):
        assert forbidden not in signature


def test_audit_covers_identity_in_both_orientations():
    audit = AUDIT.read_text(encoding="utf-8")
    for name in (
        "cmp99Eq360ComplexLocalLaplacianPerturbation",
        "cmp99Eq360_complexRegionalLaplacian_sub_eq_localPerturbation",
        "cmp99Eq360_complexRegionalLaplacian_eq_sub_localPerturbation",
    ):
        assert f"#print axioms YangMills.RG.{name}" in audit
