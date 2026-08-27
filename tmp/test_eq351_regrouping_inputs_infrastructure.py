from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]


def load(relative: str, name: str):
    path = ROOT / relative
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_contract_and_generators_share_exact_scope() -> None:
    contract = load(
        "tmp/verify_eq351_regrouping_inputs_contract.py", "eq351_input_contract_test"
    )
    runner = load(
        "tmp/generate_eq351_regrouping_inputs_runner.py", "eq351_input_runner_test"
    )
    assert contract.MODULES == runner.MODULES
    assert sum(count for _, count in contract.MODULES) == 16
    assert len(contract.stages()) == 9


def test_promotion_scope_and_retargeting() -> None:
    promoter = load(
        "tmp/promote_eq351_regrouping_inputs_compiler_gate.py",
        "eq351_input_promoter_test",
    )
    selected = promoter.selected_paths()
    assert len(selected) == 6
    assert len({promoter.destination(path) for path in selected}) == 6
    source = (
        "import tmp.Dependency.draft\n\n"
        "/-! PRE-VALIDATION: no compiler verdict. -/\n"
        "theorem kept : True := by trivial\n"
    ).encode()
    promoted = promoter.promote(source).decode()
    assert "import YangMills.RG.Dependency" in promoted
    assert "PRE-VALIDATION:" in promoted
    assert "theorem kept" in promoted


@pytest.mark.parametrize(
    ("relative", "function_name"),
    (
        ("tmp/promote_eq351_regrouping_inputs_compiler_gate.py", "promote"),
        ("tmp/promote_eq360_complex_regional_real_slice.py", "retarget_imports"),
        ("tmp/promote_eq360_complex_physical_compiler_gate.py", "retarget_imports"),
    ),
)
def test_active_promotions_reject_inline_placeholder(
    relative: str, function_name: str
) -> None:
    promoter = load(relative, "active_promoter_placeholder_test")
    source = (
        "import Mathlib\n\n"
        "/-! PRE-VALIDATION: no compiler verdict. -/\n"
        "theorem bad : True := by sorry\n"
    ).encode()
    with pytest.raises(RuntimeError, match="FORBIDDEN_PLACEHOLDER"):
        getattr(promoter, function_name)(source)


def test_sealer_scope_is_six_files() -> None:
    contract = load(
        "tmp/verify_eq351_regrouping_inputs_contract.py", "eq351_input_seal_contract"
    )
    sealer = load(
        "tmp/seal_eq351_regrouping_inputs_prevalidation.py", "eq351_input_sealer_test"
    )
    assert len(sealer.paths(contract)) == 6
