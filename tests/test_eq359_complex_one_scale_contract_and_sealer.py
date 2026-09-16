from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
CONTRACT = ROOT / "tmp" / "verify_eq359_complex_one_scale_average_contract.py"
GENERATOR = ROOT / "tmp" / "generate_eq359_complex_one_scale_average_runner.py"
SEALER = ROOT / "tmp" / "seal_eq359_complex_one_scale_average_prevalidation.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_generator_contract_and_sealer_share_exact_scope():
    contract = load(CONTRACT, "eq359_main_contract_test")
    generator = load(GENERATOR, "eq359_main_generator_test")
    sealer = load(SEALER, "eq359_main_sealer_test")
    assert generator.MODULES == contract.MODULES
    assert len(contract.MODULES) == 7
    assert sum(count for _, count in contract.MODULES) == 32
    assert len(sealer.paths(contract)) == 14
    assert len(contract.stages()) == 17


def test_sealer_accepts_only_complete_32_declaration_evidence(tmp_path: Path):
    sealer = load(SEALER, "eq359_main_sealer_evidence_test")
    evidence = tmp_path / "evidence.json"
    payload = {
        "status": "EQ359_COMPLEX_ONE_SCALE_AVERAGE_EVIDENCE_OK",
        "expected_declarations": 32,
        "source_sha": "1" * 40,
        "boundary_blob_sha256": {},
    }
    evidence.write_text(json.dumps(payload), encoding="utf-8")
    assert sealer.read_evidence(evidence)["expected_declarations"] == 32
    payload["expected_declarations"] = 31
    evidence.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(RuntimeError, match="DECLARATIONS_MISMATCH"):
        sealer.read_evidence(evidence)

