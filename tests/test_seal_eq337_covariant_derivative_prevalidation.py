from __future__ import annotations

import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SEALER = ROOT / "tmp" / "seal_eq337_covariant_derivative_prevalidation.py"


def load_sealer():
    spec = importlib.util.spec_from_file_location("eq337_coordinate_sealer_test", SEALER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_scope_is_exact_three_source_audit_pairs() -> None:
    sealer = load_sealer()
    assert len(sealer.MODULES) == 3
    assert len(sealer.paths()) == 6
    assert len(set(sealer.paths())) == 6


def test_sealed_core_adds_each_audit_once() -> None:
    sealer = load_sealer()
    sealed = sealer.sealed_core(b"import YangMills.RG.BalabanCMP99Source\n").decode()
    for module in sealer.MODULES:
        assert sealed.count(f"import YangMills.RG.{module}Audit") == 1


def test_evidence_contract_requires_all_57_declarations(tmp_path: Path) -> None:
    sealer = load_sealer()
    evidence = tmp_path / "evidence.json"
    payload = {
        "status": "EQ337_COVARIANT_DERIVATIVE_EVIDENCE_OK",
        "expected_declarations": 57,
        "source_sha": "1" * 40,
        "boundary_blob_sha256": {},
    }
    evidence.write_text(json.dumps(payload), encoding="utf-8")
    assert sealer.read_evidence(evidence)["expected_declarations"] == 57
    payload["expected_declarations"] = 31
    evidence.write_text(json.dumps(payload), encoding="utf-8")
    try:
        sealer.read_evidence(evidence)
    except RuntimeError as exc:
        assert "DECLARATIONS_MISMATCH" in str(exc)
    else:
        raise AssertionError("partial 31-declaration evidence was accepted")
