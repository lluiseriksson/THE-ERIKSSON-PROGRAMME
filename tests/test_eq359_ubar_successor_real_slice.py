from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99ComplexUbarSuccessorRealSlice.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99ComplexUbarSuccessorRealSliceAudit.draft.lean"
MANIFEST = ROOT / "tmp" / "EQ359-UBAR-SUCCESSOR-REAL-SLICE-DRAFT-PATHS.txt"


def test_source_keeps_prevalidation_and_canonical_boundary():
    text = SOURCE.read_text(encoding="utf-8")
    assert "PRE-VALIDATION" in text
    assert "cmp99SourceComplexLocalizedNextBackground_realSlice" in text
    assert "cmp99PhysicalUbarGaugeConfigOfDeviationBudget" in text
    assert "cmp99SourceLocalizedNextBackground" not in text


def test_budgets_are_independent_proof_inputs():
    text = SOURCE.read_text(encoding="utf-8")
    assert "Bcomplex Bphysical" in text
    assert "cmp99UbarSpecialLinearBlockOfDeviationBudget_realSlice" in text
    assert "No equality of budgets is assumed" in text


def test_audit_and_manifest_cover_exact_draft_pair():
    audit = AUDIT.read_text(encoding="utf-8")
    assert audit.count("#print axioms") == 6
    paths = [line for line in MANIFEST.read_text(encoding="utf-8").splitlines()
             if line.strip()]
    assert paths == [
        "tmp/BalabanCMP99ComplexUbarSuccessorRealSlice.draft.lean",
        "tmp/BalabanCMP99ComplexUbarSuccessorRealSliceAudit.draft.lean",
    ]
