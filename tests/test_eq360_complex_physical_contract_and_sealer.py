from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
CONTRACT = ROOT / "tmp" / "verify_eq360_complex_physical_contract.py"
SEALER = ROOT / "tmp" / "seal_eq360_complex_physical_prevalidation.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_contract_has_exact_scope_and_terminal_root():
    contract = load(CONTRACT, "eq360_contract_test")
    assert len(contract.MODULES) == 4
    assert sum(count for _, count in contract.MODULES) == 28
    assert contract.stages()[0] == "eq360_complex_physical_materialize_dependencies"
    assert contract.stages()[-1] == "eq360_complex_physical_root"
    assert len(contract.stages()) == 11


def test_sealer_scope_matches_contract():
    contract = load(CONTRACT, "eq360_contract_scope_test")
    sealer = load(SEALER, "eq360_sealer_scope_test")
    assert set(sealer.paths(contract)) == {
        f"YangMills/RG/{module}{suffix}.lean"
        for module, _ in contract.MODULES
        for suffix in ("", "Audit")
    }


def test_sealer_rejects_wrong_status_and_count(tmp_path):
    sealer = load(SEALER, "eq360_sealer_status_test")
    bad_status = tmp_path / "bad-status.json"
    bad_status.write_text(json.dumps({"status": "PASS"}), encoding="utf-8")
    with pytest.raises(RuntimeError, match="STATUS_MISMATCH"):
        sealer.read_evidence(bad_status)
    bad_count = tmp_path / "bad-count.json"
    bad_count.write_text(json.dumps({
        "status": "EQ360_COMPLEX_PHYSICAL_EVIDENCE_OK",
        "expected_declarations": 27,
    }), encoding="utf-8")
    with pytest.raises(RuntimeError, match="DECLARATIONS_MISMATCH"):
        sealer.read_evidence(bad_count)
