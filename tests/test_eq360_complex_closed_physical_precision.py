from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99Eq360ComplexClosedPhysicalPrecision.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99Eq360ComplexClosedPhysicalPrecisionAudit.draft.lean"


def test_source_precision_constructs_every_operator_internally():
    text = SOURCE.read_text(encoding="utf-8")
    assert "cmp99Eq359SourceComplexClosedPhysicalTowerPair" in text
    assert "cmp99Eq360ComplexRegionalLaplacian Omega S.background0" in text
    assert "cmp99Eq360ComplexRegionalLaplacian Omega S.background1" in text
    assert "S.towerPair.Q0" in text
    assert "S.towerPair.Q1" in text
    assert "S.towerPair.starred0" in text
    assert "S.towerPair.starred1" in text
    assert "cmp99Eq360ComplexLocalLaplacianPerturbation Omega" in text
    assert "S.localLaplacianPerturbation" in text
    assert "S.sourcePrecisionPerturbation" in text


def test_input_has_no_free_operator_or_finished_identity():
    text = SOURCE.read_text(encoding="utf-8")
    structure = text.split(
        "structure CMP99Eq360ComplexClosedPhysicalInput", 1
    )[1].split("namespace CMP99Eq360ComplexClosedPhysicalInput", 1)[0]
    for forbidden in ("Delta0", "Delta1", "Q0", "Q1", "F2", "precision_eq"):
        assert forbidden not in structure


def test_audit_covers_source_specific_boundary():
    audit = AUDIT.read_text(encoding="utf-8")
    names = [
        "CMP99Eq360ComplexClosedPhysicalInput",
        "CMP99Eq360ComplexClosedPhysicalInput.background0",
        "CMP99Eq360ComplexClosedPhysicalInput.background1",
        "CMP99Eq360ComplexClosedPhysicalInput.towerPair",
        "CMP99Eq360ComplexClosedPhysicalInput.baselineLaplacian",
        "CMP99Eq360ComplexClosedPhysicalInput.perturbedLaplacian",
        "CMP99Eq360ComplexClosedPhysicalInput.localLaplacianPerturbation",
        "CMP99Eq360ComplexClosedPhysicalInput.baselinePrecision",
        "CMP99Eq360ComplexClosedPhysicalInput.perturbedPrecision",
        "CMP99Eq360ComplexClosedPhysicalInput.precisionPerturbation",
        "CMP99Eq360ComplexClosedPhysicalInput.sourcePrecisionPerturbation",
        "CMP99Eq360ComplexClosedPhysicalInput.precisionPerturbation_eq_sourcePrecisionPerturbation",
        "CMP99Eq360ComplexClosedPhysicalInput.perturbedPrecision_eq_baselinePrecision_sub_perturbation",
        "CMP99Eq360ComplexClosedPhysicalInput.perturbedPrecision_eq_baselinePrecision_sub_sourcePerturbation",
    ]
    for name in names:
        assert f"#print axioms YangMills.RG.{name}" in audit
