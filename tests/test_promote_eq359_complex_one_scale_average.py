from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
PROMOTER = ROOT / "tmp" / "promote_eq359_complex_one_scale_average.py"
SEALER = ROOT / "tmp" / "seal_eq359_complex_one_scale_average_prevalidation.py"
CONTRACT = ROOT / "tmp" / "verify_eq359_complex_one_scale_average_contract.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_promotion_scope_is_exactly_seven_source_audit_pairs() -> None:
    promoter = load(PROMOTER, "eq359_promoter_test")
    selected = promoter.paths()
    assert len(selected) == 14
    assert len(set(selected)) == 14
    assert all(path.startswith("tmp/") and path.endswith(".draft.lean") for path in selected)
    destinations = [promoter.destination(path) for path in selected]
    assert len(set(destinations)) == 14
    assert all(path.startswith("YangMills/RG/") for path in destinations)


def test_import_retarget_preserves_exact_prevalidation_notice() -> None:
    promoter = load(PROMOTER, "eq359_promoter_import_test")
    source = (
        "import tmp.Upstream.draft\n"
        "/-!\nPRE-VALIDATION: source present; not compiler-verified.\n-/\n"
    ).encode()
    result = promoter.retarget_imports(source).decode()
    assert "import YangMills.RG.Upstream" in result
    assert "import tmp." not in result
    assert result.count("PRE-VALIDATION:") == 1


def test_import_retarget_rejects_missing_notice() -> None:
    promoter = load(PROMOTER, "eq359_promoter_reject_test")
    with pytest.raises(RuntimeError, match="PREVALIDATION_COUNT_MISMATCH"):
        promoter.retarget_imports(b"import tmp.Upstream.draft\n")


def test_core_scope_is_exactly_seven_audits() -> None:
    promoter = load(PROMOTER, "eq359_promoter_core_test")
    selected = promoter.paths()
    result = promoter.core_with_audits(b"import Mathlib\n", selected).decode()
    imports = [line for line in result.splitlines() if line.startswith("import YangMills.RG.")]
    assert len(imports) == 7
    assert len(set(imports)) == 7
    assert all(line.endswith("Audit") for line in imports)


def test_sealer_scope_matches_promoted_scope() -> None:
    promoter = load(PROMOTER, "eq359_promoter_scope_test")
    sealer = load(SEALER, "eq359_sealer_scope_test")
    contract = load(CONTRACT, "eq359_contract_scope_test")
    assert set(sealer.paths(contract)) == {
        promoter.destination(path) for path in promoter.paths()
    }
