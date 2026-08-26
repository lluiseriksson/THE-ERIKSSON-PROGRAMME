from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = (
    ROOT / "tmp" / "BalabanCMP99SpecialUnitaryToSpecialLinearRealSlice.draft.lean"
)
AUDIT = (
    ROOT
    / "tmp"
    / "BalabanCMP99SpecialUnitaryToSpecialLinearRealSliceAudit.draft.lean"
)


def test_real_slice_builds_the_canonical_group_hom_internally() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    assert text.count("PRE-VALIDATION:") == 1
    assert "SUN Nc →* Matrix.SpecialLinearGroup (Fin Nc) ℂ" in text
    assert "toFun g := ⟨g.1, (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2⟩" in text
    assert "(inclusion" not in text
    assert "(hinclusion" not in text


def test_real_slice_proves_inverse_and_action_agreement() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    assert "theorem cmp99SUNToSpecialLinear_inv_coe" in text
    assert "theorem cmp99SpecialLinearAdjointCoordLM_realSlice" in text
    assert "theorem cmp99SpecialLinearAdjointCoordLM_realSlice_inv" in text
    assert "cmp98LieCoordMatrix_adCLM" in text
    assert "cmp99SUNLieComplexCoordMatrixLM_injective" in text
    assert "(matrixSUNAdjointModel Nc).adCLM g⁻¹ X" in text


def test_real_slice_audit_covers_every_public_declaration() -> None:
    text = AUDIT.read_text(encoding="utf-8")
    assert text.count("PRE-VALIDATION:") == 1
    assert text.count("#print axioms ") == 5
    for declaration in (
        "cmp99SUNToSpecialLinear",
        "cmp99SUNToSpecialLinear_coe",
        "cmp99SUNToSpecialLinear_inv_coe",
        "cmp99SpecialLinearAdjointCoordLM_realSlice",
        "cmp99SpecialLinearAdjointCoordLM_realSlice_inv",
    ):
        assert f"#print axioms YangMills.RG.{declaration}" in text
