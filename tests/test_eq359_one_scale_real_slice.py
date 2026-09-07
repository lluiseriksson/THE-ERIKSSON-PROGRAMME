from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99Eq359OneScaleRealSlice.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99Eq359OneScaleRealSliceAudit.draft.lean"


def test_one_scale_real_slice_constructs_complex_holonomy() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    assert text.count("PRE-VALIDATION:") == 1
    assert "def cmp99SUNHolonomyToSpecialLinear" in text
    assert "cmp99SUNToSpecialLinear Nc (holonomy y x)" in text
    assert "(complexHolonomy" not in text
    assert "(htransport" not in text


def test_one_scale_real_slice_keeps_both_printed_masses_visible() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    assert "cmp99ComplexAdjointBlockAverageCLM_realSlice" in text
    assert "cmp99SourceBlockAverageWeight M d" in text
    assert "cmp99ComplexAdjointBlockStarSynthesisCLM_realSlice" in text
    assert "cmp99AdjointBlockSynthesisCLM Omega hOmega 1" in text
    assert "cmp99SpecialLinearAdjointCoordLM_realSlice_inv" in text


def test_one_scale_real_slice_audit_is_complete() -> None:
    text = AUDIT.read_text(encoding="utf-8")
    assert text.count("PRE-VALIDATION:") == 1
    assert text.count("#print axioms ") == 4
    for declaration in (
        "cmp99SUNHolonomyToSpecialLinear",
        "cmp99SUNHolonomyToSpecialLinear_apply",
        "cmp99ComplexAdjointBlockAverageCLM_realSlice",
        "cmp99ComplexAdjointBlockStarSynthesisCLM_realSlice",
    ):
        assert f"#print axioms YangMills.RG.{declaration}" in text
