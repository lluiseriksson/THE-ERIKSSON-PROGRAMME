from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_changed_run_coverage",
    ROOT / "scripts" / "validate_changed_run_coverage.py",
)
assert SPEC and SPEC.loader
validator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = validator
SPEC.loader.exec_module(validator)


def write_manifest(directory: Path, output: str) -> None:
    directory.mkdir(parents=True)
    (directory / "run.json").write_text(
        json.dumps({"outputs": [{"path": output}]}), encoding="utf-8"
    )


def test_repository_branch_has_no_uncovered_changed_artifacts() -> None:
    changes = validator.git_changes(ROOT, "origin/main")
    assert validator.validate_changed_coverage(changes) == []


def test_changed_transcript_requires_manifest(tmp_path: Path) -> None:
    changes = [("M", "scripts/cascade9_transcript.txt")]
    errors = validator.validate_changed_coverage(changes, tmp_path / "run-manifests")
    assert any("not listed" in error for error in errors)


def test_manifest_output_covers_changed_transcript(tmp_path: Path) -> None:
    manifests = tmp_path / "run-manifests"
    write_manifest(manifests, "scripts/cascade9_transcript.txt")
    changes = [("A", "scripts/cascade9_transcript.txt")]
    assert validator.validate_changed_coverage(changes, manifests) == []


def test_deleted_or_noncomputational_files_do_not_require_manifest(tmp_path: Path) -> None:
    changes = [
        ("D", "scripts/old_transcript.txt"),
        ("M", "scripts/cascade9.py"),
        ("M", "papers/example.pdf"),
        ("M", "docs/SURFACE-CLOSURE-NOTES.md"),
    ]
    assert validator.validate_changed_coverage(changes, tmp_path / "missing") == []


def test_renamed_artifact_uses_destination_path(tmp_path: Path) -> None:
    manifests = tmp_path / "run-manifests"
    write_manifest(manifests, "scripts/new_output.txt")
    changes = [("R100", "scripts/new_output.txt")]
    assert validator.validate_changed_coverage(changes, manifests) == []
