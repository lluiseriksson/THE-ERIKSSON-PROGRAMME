from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation.draft.lean"
AUDIT = ROOT / "tmp" / "BalabanCMP99Eq360ComplexRegionalPrecisionPerturbationAudit.draft.lean"


def test_eq360_complex_leaf_keeps_printed_star_independent() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    assert text.count("PRE-VALIDATION:") == 1
    assert "T.F2star.comp T.Q0" in text
    assert "T.starred0.comp T.F2" in text
    assert "T.F2star.comp T.F2" in text
    assert ".adjoint" not in text


def test_eq360_complex_leaf_does_not_accept_finished_perturbations() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    signature = text.split(
        "def cmp99Eq360ComplexRegionalPrecisionPerturbation", 1
    )[1].split("\n  (Delta0 - Delta1)", 1)[0]
    assert "(T : CMP99Eq359ComplexRegionalTowerPair" in signature
    assert "(Delta0 Delta1" in signature
    assert "(Q0" not in signature
    assert "(Q1" not in signature
    assert "(F2" not in signature
    assert "(F2star" not in signature


def test_eq360_complex_audit_covers_all_public_declarations() -> None:
    text = AUDIT.read_text(encoding="utf-8")
    assert text.count("PRE-VALIDATION:") == 1
    assert text.count("#print axioms ") == 3
    for declaration in (
        "cmp99Eq360ComplexRegionalPrecision",
        "cmp99Eq360ComplexRegionalPrecisionPerturbation",
        "cmp99Eq360_complexRegionalPrecision_eq_sub_perturbation",
    ):
        assert f"#print axioms YangMills.RG.{declaration}" in text
