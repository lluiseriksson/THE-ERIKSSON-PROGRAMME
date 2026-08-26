from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "BalabanCMP99ComplexPhysicalRegionalTower.draft.lean"


def test_complex_physical_holonomy_uses_the_generic_path_operation() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    body = text.split("def cmp99ComplexPhysicalBlockHolonomy", 1)[1].split(
        "/-- Analytic tower indexed", 1
    )[0]
    assert "Matrix.SpecialLinearGroup (Fin Nc) ℂ" in body
    assert ").holonomy background" in body
    assert "cmp99ContourHolonomy" not in body


def test_complex_physical_tower_remains_prevalidation() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    assert text.count("PRE-VALIDATION:") == 1
