from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99Eq359TowerRealSliceAgreement.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99Eq359TowerRealSliceAgreementAudit.draft.lean"
MANIFEST = ROOT / "tmp" / "EQ359-TOWER-REAL-SLICE-AGREEMENT-DRAFT-PATHS.txt"


def test_relation_carries_both_forward_and_starred_equalities():
    text = SOURCE.read_text(encoding="utf-8")
    assert "terminalComplexification" in text
    assert "Qprime_realSlice" in text
    assert "starred_realSlice" in text
    assert "CMP99Eq359TowerRealSliceAgreement.stop" in text
    assert "CMP99Eq359TowerRealSliceAgreement.step" in text


def test_step_uses_literal_one_scale_real_slice_and_both_masses():
    text = SOURCE.read_text(encoding="utf-8")
    assert "cmp99ComplexAdjointBlockAverageCLM_realSlice" in text
    assert "cmp99ComplexAdjointBlockStarSynthesisCLM_realSlice" in text
    assert "cmp99SourceTransportedBlockAverageCLM" in text
    assert "cmp99SourceTransportedBlockWeightedAdjointCLM" in text
    assert "matrixSUNAdjointModel Nc" in text


def test_audit_and_manifest_are_exact():
    assert AUDIT.read_text(encoding="utf-8").count("#print axioms") == 3
    paths = [line for line in MANIFEST.read_text(encoding="utf-8").splitlines()
             if line.strip()]
    assert paths == [
        "tmp/BalabanCMP99Eq359TowerRealSliceAgreement.draft.lean",
        "tmp/BalabanCMP99Eq359TowerRealSliceAgreementAudit.draft.lean",
    ]
