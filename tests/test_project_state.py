from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_project_state", ROOT / "scripts" / "validate_project_state.py"
)
assert SPEC and SPEC.loader
validator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = validator
SPEC.loader.exec_module(validator)


MATHLIB = "0" * 40


def repo_fixture(root: Path) -> dict:
    (root / "docs").mkdir(parents=True)
    for name in ("VERIFICATION-LEDGER.md",):
        (root / "docs" / name).write_text("evidence\n", encoding="utf-8")
    (root / "HYPOTHESIS_FRONTIER.md").write_text("frontier\n", encoding="utf-8")
    (root / "HORIZON.md").write_text("continuum\n", encoding="utf-8")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.test\n", encoding="utf-8")
    (root / "lakefile.lean").write_text(
        'require mathlib from git\n  "https://example.invalid/mathlib" @\n    "'
        + MATHLIB
        + '"\n',
        encoding="utf-8",
    )
    (root / "lake-manifest.json").write_text(
        json.dumps(
            {
                "packages": [
                    {
                        "name": "mathlib",
                        "rev": MATHLIB,
                        "inputRev": MATHLIB,
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    return {
        "schema_version": 1,
        "lean_core": {
            "source_checkpoint": "abcdef0",
            "toolchain": "leanprover/lean4:v4.test",
            "mathlib_commit": MATHLIB,
            "latest_recorded_build": {
                "status": "green",
                "jobs": 1,
                "evidence": "docs/VERIFICATION-LEDGER.md",
            },
            "allowed_oracle": ["propext", "Classical.choice", "Quot.sound"],
        },
        "frontier": {
            "id": "hRpoly",
            "status": "explicit_theorem_hypothesis",
            "evidence": "HYPOTHESIS_FRONTIER.md",
        },
        "continuum": {
            "status": "open",
            "statement": "No proved continuum construction.",
            "evidence": "HORIZON.md",
        },
    }


def accepts_checkpoint(_root: Path, _commit: str) -> bool:
    return True


def test_repository_project_state_is_valid() -> None:
    data = json.loads((ROOT / "project-state.json").read_text(encoding="utf-8"))
    assert validator.validate_state(data, ROOT) == []


def test_valid_project_state_fixture(tmp_path: Path) -> None:
    data = repo_fixture(tmp_path)
    assert validator.validate_state(data, tmp_path, accepts_checkpoint) == []


def test_toolchain_drift_is_fatal(tmp_path: Path) -> None:
    data = repo_fixture(tmp_path)
    data["lean_core"]["toolchain"] = "leanprover/lean4:wrong"
    errors = validator.validate_state(data, tmp_path, accepts_checkpoint)
    assert any("does not match lean-toolchain" in error for error in errors)


def test_mathlib_manifest_drift_is_fatal(tmp_path: Path) -> None:
    data = repo_fixture(tmp_path)
    manifest = json.loads((tmp_path / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest["packages"][0]["inputRev"] = "1" * 40
    (tmp_path / "lake-manifest.json").write_text(
        json.dumps(manifest), encoding="utf-8"
    )
    errors = validator.validate_state(data, tmp_path, accepts_checkpoint)
    assert any("rev/inputRev" in error for error in errors)


def test_missing_or_non_ancestor_checkpoint_is_fatal(tmp_path: Path) -> None:
    data = repo_fixture(tmp_path)
    errors = validator.validate_state(data, tmp_path, lambda _root, _commit: False)
    assert any("missing or not an ancestor" in error for error in errors)


def test_continuum_cannot_be_promoted_silently(tmp_path: Path) -> None:
    data = repo_fixture(tmp_path)
    data["continuum"]["status"] = "proved"
    errors = validator.validate_state(data, tmp_path, accepts_checkpoint)
    assert any("continuum.status: expected open" in error for error in errors)
