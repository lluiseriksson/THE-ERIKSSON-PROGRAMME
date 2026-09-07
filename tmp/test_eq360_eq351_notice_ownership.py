"""Static ownership checks for the Eq360/Eq351 PRE-VALIDATION boundary."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load(relative: str, name: str):
    path = ROOT / relative
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def module_paths(modules) -> set[str]:
    return {
        f"YangMills/RG/{module}{suffix}.lean"
        for module, _ in modules
        for suffix in ("", "Audit")
    }


def test_live_notice_writers_are_disjoint_and_cover_eq351_prerequisites():
    adjoint = load(
        "tmp/verify_eq351_adjoint_composition_contract.py",
        "eq351_adjoint_contract",
    )
    physical = load(
        "tmp/verify_eq360_complex_physical_contract.py",
        "eq360_physical_contract",
    )
    promoter = load(
        "tmp/promote_eq351_regrouping_inputs_compiler_gate.py",
        "eq351_regrouping_promoter",
    )

    adjoint_paths = module_paths(adjoint.MODULES)
    physical_paths = module_paths(physical.MODULES)
    assert len(adjoint_paths) == 4
    assert len(physical_paths) == 10
    assert adjoint_paths.isdisjoint(physical_paths)

    regional_physical_paths = {
        path
        for path in physical_paths
        if "Eq360ComplexRegionalLaplacian" in path
    }
    assert len(regional_physical_paths) == 4
    assert set(promoter.SEALED_REGIONAL_GATE) == (
        adjoint_paths | regional_physical_paths
    )


def test_overlapping_legacy_regional_sealer_is_fail_closed():
    text = (
        ROOT / "tmp/seal_eq360_complex_regional_prevalidation.py"
    ).read_text(encoding="utf-8")
    assert "EQ360_COMPLEX_REGIONAL_SEAL_SUPERSEDED=" in text
    assert "seal_eq351_adjoint_composition_prevalidation.py" in text
    assert "seal_eq360_complex_physical_prevalidation.py" in text

