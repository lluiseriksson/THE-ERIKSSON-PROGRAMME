from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
PROMOTER = ROOT / "tmp" / "promote_eq360_complex_physical_compiler_gate.py"


def load():
    spec = importlib.util.spec_from_file_location("eq360_promoter_test", PROMOTER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_promotion_scope_is_five_source_audit_pairs():
    promoter = load()
    selected = promoter.paths()
    assert len(selected) == 10
    assert len(set(selected)) == 10
    destinations = [promoter.destination(path) for path in selected]
    assert len(set(destinations)) == 10
    assert all(path.startswith("YangMills/RG/") for path in destinations)


def test_import_retarget_is_exact_and_fail_closed():
    promoter = load()
    source = (
        "import tmp.Upstream.draft\n"
        "/-!\nPRE-VALIDATION: source present; not compiler-verified.\n-/\n"
    ).encode()
    result = promoter.retarget_imports(source).decode()
    assert "import YangMills.RG.Upstream" in result
    assert "import tmp." not in result
    assert result.count("PRE-VALIDATION:") == 1
    with pytest.raises(RuntimeError, match="PREVALIDATION_COUNT_MISMATCH"):
        promoter.retarget_imports(b"import tmp.Upstream.draft\n")


def test_core_adds_exactly_five_audits():
    promoter = load()
    result = promoter.core_with_audits(b"import Mathlib\n", promoter.paths()).decode()
    imports = [
        line for line in result.splitlines()
        if line.startswith("import YangMills.RG.")
    ]
    assert len(imports) == 5
    assert len(set(imports)) == 5
    assert all(line.endswith("Audit") for line in imports)


def test_prerequisite_set_contains_complex_and_real_slice_boundaries():
    promoter = load()
    assert "YangMills/RG/BalabanCMP99Eq359ComplexClosedPhysicalTowerPair.lean" in promoter.REQUIRED_PREREQUISITES
    assert "YangMills/RG/BalabanCMP99Eq359TowerRealSliceAgreement.lean" in promoter.REQUIRED_PREREQUISITES
    assert "YangMills/RG/BalabanCMP99SpecialUnitaryToSpecialLinearRealSlice.lean" in promoter.REQUIRED_PREREQUISITES
