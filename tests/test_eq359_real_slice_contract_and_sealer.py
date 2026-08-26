from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
CONTRACT = ROOT / "tmp" / "verify_eq359_real_slice_contract.py"
SEALER = ROOT / "tmp" / "seal_eq359_real_slice_prevalidation.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_contract_has_exact_twenty_declarations_and_terminal_root():
    contract = load(CONTRACT, "eq359_real_slice_contract_test")
    assert len(contract.MODULES) == 4
    assert sum(count for _, count in contract.MODULES) == 20
    stages = contract.stages()
    assert stages[0] == "eq359_real_slice_materialize_dependencies"
    assert stages[-1] == "eq359_real_slice_root"
    assert len(stages) == 11


def test_sealer_scope_matches_contract():
    contract = load(CONTRACT, "eq359_real_slice_contract_scope_test")
    sealer = load(SEALER, "eq359_real_slice_sealer_scope_test")
    assert set(sealer.paths(contract)) == {
        f"YangMills/RG/{module}{suffix}.lean"
        for module, _ in contract.MODULES
        for suffix in ("", "Audit")
    }


def test_sealer_rejects_wrong_status_and_count(tmp_path):
    sealer = load(SEALER, "eq359_real_slice_sealer_status_test")
    bad_status = tmp_path / "bad-status.json"
    bad_status.write_text(json.dumps({"status": "PASS"}), encoding="utf-8")
    with pytest.raises(RuntimeError, match="STATUS_MISMATCH"):
        sealer.read_evidence(bad_status)
    bad_count = tmp_path / "bad-count.json"
    bad_count.write_text(json.dumps({
        "status": "EQ359_REAL_SLICE_EVIDENCE_OK",
        "expected_declarations": 19,
    }), encoding="utf-8")
    with pytest.raises(RuntimeError, match="DECLARATIONS_MISMATCH"):
        sealer.read_evidence(bad_count)
