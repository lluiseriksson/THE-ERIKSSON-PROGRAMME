from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SEALER = ROOT / "tmp" / "seal_eq337_complex_perturbed_background_prevalidation.py"


def load_sealer():
    spec = importlib.util.spec_from_file_location("eq337_base_sealer", SEALER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_boundary_is_the_tracked_source_and_audit_pair() -> None:
    sealer = load_sealer()
    verifier = sealer.load_verifier()
    assert sealer.boundary_paths(verifier) == [
        "YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbedBackground.lean",
        "YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbedBackgroundAudit.lean",
    ]


def test_remove_multiline_source_notice_preserves_module_documentation() -> None:
    sealer = load_sealer()
    source = (
        "import Mathlib\n\n"
        "/-!\n"
        "PRE-VALIDATION: source has no materialized `.olean` and no\n"
        "compiler or axiom-oracle verdict.\n\n"
        "# Retained title\n\n"
        "Retained documentation.\n"
        "-/\n\n"
        "theorem kept : True := by trivial\n"
    ).encode()
    sealed = sealer.remove_prevalidation_block(source, "source.lean").decode()
    assert "PRE-VALIDATION:" not in sealed
    assert "# Retained title" in sealed
    assert "Retained documentation." in sealed
    assert "theorem kept" in sealed


def test_remove_single_line_audit_notice_removes_empty_doc_block() -> None:
    sealer = load_sealer()
    audit = (
        "import Mathlib\n\n"
        "/-! PRE-VALIDATION: scratch audit; no compiler verdict. -/\n\n"
        "#print axioms Nat.add_comm\n"
    ).encode()
    sealed = sealer.remove_prevalidation_block(audit, "audit.lean").decode()
    assert "PRE-VALIDATION:" not in sealed
    assert "/-!" not in sealed
    assert "#print axioms Nat.add_comm" in sealed


def test_remove_notice_rejects_missing_or_ambiguous_scope() -> None:
    sealer = load_sealer()
    with pytest.raises(RuntimeError, match="PREVALIDATION_BLOCK_COUNT"):
        sealer.remove_prevalidation_block(b"import Mathlib\n", "missing.lean")
    with pytest.raises(RuntimeError, match="PREVALIDATION_BLOCK_COUNT"):
        sealer.remove_prevalidation_block(
            b"/-! PRE-VALIDATION: one. -/\n/-! PRE-VALIDATION: two. -/\n",
            "ambiguous.lean",
        )


def test_current_checkpoint_is_an_explicit_cli_input() -> None:
    text = SEALER.read_text(encoding="utf-8")
    assert 'parser.add_argument("--current-source-sha")' in text
    assert "EQ337_BASE_EVIDENCE_BLOB_DRIFT" in text
    assert "git_blob(current_source_sha, CORE)" in text
