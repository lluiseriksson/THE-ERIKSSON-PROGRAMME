from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99PhysicalBackgroundRealSlice.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99PhysicalBackgroundRealSliceAudit.draft.lean"


def test_background_embedding_is_constructed_pointwise() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    assert text.count("PRE-VALIDATION:") == 1
    assert "def cmp99PhysicalGaugeBackgroundToSpecialLinear" in text
    assert "toFun e := cmp99SUNToSpecialLinear Nc (U e)" in text
    assert "map_reverse e := by" in text
    assert "(embeddedBackground" not in text
    assert "(hbackground" not in text


def test_contour_agreement_uses_the_shared_physical_edge_list() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    body = text.split(
        "theorem cmp99ComplexPhysicalBlockHolonomy_realSlice", 1
    )[1]
    assert "cmp99BlockContainedContourSystem (G := SUN Nc)" in body
    assert "physical.edges" in body
    assert "wilsonLine_cmp99PhysicalGaugeBackgroundToSpecialLinear" in body
    assert "(hcontour" not in body


def test_real_perturbation_builds_the_full_background_agreement() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    body = text.split(
        "theorem cmp99Eq337PhysicalComplexPerturbedBackground_realSlice", 1
    )[1]
    assert "cmp98PhysicalSuLeftVariation U A eta" in body
    assert "cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix_realSlice" in body
    assert "cases sign" in body
    assert "rw [map_inv, hpos]" in body
    assert "(hbackground" not in body


def test_background_real_slice_audit_is_complete() -> None:
    text = AUDIT.read_text(encoding="utf-8")
    assert text.count("PRE-VALIDATION:") == 1
    assert text.count("#print axioms ") == 5
    for declaration in (
        "cmp99PhysicalGaugeBackgroundToSpecialLinear",
        "cmp99PhysicalGaugeBackgroundToSpecialLinear_apply",
        "wilsonLine_cmp99PhysicalGaugeBackgroundToSpecialLinear",
        "cmp99ComplexPhysicalBlockHolonomy_realSlice",
        "cmp99Eq337PhysicalComplexPerturbedBackground_realSlice",
    ):
        assert f"#print axioms YangMills.RG.{declaration}" in text
