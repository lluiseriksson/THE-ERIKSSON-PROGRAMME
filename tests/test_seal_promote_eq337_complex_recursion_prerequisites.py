from __future__ import annotations

import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "seal_promote_eq337_complex_recursion_prerequisites.py"


def load_script():
    spec = importlib.util.spec_from_file_location("eq337_prereq_seal", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_exact_promotion_scope_excludes_mathlib_repro() -> None:
    script = load_script()
    assert script.UBAR_EXPECTED_DECLARATIONS == 79
    assert script.RECURSION_EXPECTED_DECLARATIONS == 16
    verifier = script.load_module(
        script.RECURSION_VERIFIER, "test_eq337_recursion_verifier"
    )
    assert len(script.ubar_paths()) == 14
    recursion = script.recursion_paths(verifier)
    assert len(recursion) == 4
    assert all(path.endswith(".draft.lean") for path in recursion)
    assert all("repro" not in path.lower() for path in recursion)
    assert len({script.destination(path) for path in [*script.ubar_paths(), *recursion]}) == 18


def test_core_import_scope_is_exactly_nine_audits() -> None:
    script = load_script()
    verifier = script.load_module(
        script.RECURSION_VERIFIER, "test_eq337_recursion_verifier_for_core"
    )
    sealed = script.sealed_core(b"import Mathlib\n", verifier).decode()
    imports = [line for line in sealed.splitlines() if line.startswith("import YangMills.RG.")]
    assert len(imports) == 9
    assert len(set(imports)) == 9
    assert all(line.endswith("Audit") for line in imports)
    assert not any("repro" in line.lower() for line in imports)


def test_destination_maps_only_draft_modules() -> None:
    script = load_script()
    assert script.destination("tmp/ExampleAudit.draft.lean") == (
        "YangMills/RG/ExampleAudit.lean"
    )


def test_read_evidence_rejects_nonhex_source_sha(tmp_path: Path) -> None:
    script = load_script()
    evidence = tmp_path / "evidence.json"
    evidence.write_text(
        json.dumps(
            {
                "status": "OK",
                "source_sha": "z" * 40,
                "expected_declarations": 1,
                "boundary_blob_sha256": {},
            }
        ),
        encoding="utf-8",
    )
    with pytest.raises(RuntimeError, match="EVIDENCE_SOURCE_INVALID"):
        script.read_evidence(evidence, "OK", 1)


def test_evidence_lineage_rejects_unrelated_commits(monkeypatch) -> None:
    script = load_script()
    older = "1" * 40
    newer = "2" * 40

    def fake_git(*args: str):
        if args[:1] == ("rev-parse",):
            source = args[1].removesuffix("^{commit}")
            return SimpleNamespace(returncode=0, stdout=(source + "\n").encode())
        assert args == ("merge-base", "--is-ancestor", older, newer)
        return SimpleNamespace(returncode=1, stdout=b"")

    monkeypatch.setattr(script, "run_git", fake_git)
    with pytest.raises(RuntimeError, match="EVIDENCE_LINEAGE_MISMATCH"):
        script.require_evidence_lineage(older, newer)
