from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_run_manifests", ROOT / "scripts" / "validate_run_manifests.py"
)
assert SPEC and SPEC.loader
validator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = validator
SPEC.loader.exec_module(validator)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest(root: Path, run_id: str, status: str = "current") -> dict:
    script = root / "scripts" / "run.py"
    output = root / "outputs" / f"{run_id}.txt"
    script.parent.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    script.write_text("print('run')\n", encoding="utf-8")
    output.write_text("evidence\n", encoding="utf-8")
    return {
        "schema_version": 1,
        "run_id": run_id,
        "claim_scope": "test fixture only",
        "status": status,
        "started_utc": "2026-07-11T18:00:00Z",
        "finished_utc": "2026-07-11T18:01:00Z",
        "command": ["python", "scripts/run.py"],
        "working_directory": ".",
        "script": {"path": "scripts/run.py", "sha256": digest(script)},
        "environment": {"python": "3.12", "libraries": {}},
        "inputs": [],
        "outputs": [
            {"path": f"outputs/{run_id}.txt", "sha256": digest(output)}
        ],
        "supersedes": [],
        "superseded_by": None,
        "quarantine_reason": None,
    }


def write_manifest(root: Path, data: dict) -> None:
    directory = root / "run-manifests"
    directory.mkdir(parents=True, exist_ok=True)
    (directory / f"{data['run_id']}.json").write_text(
        json.dumps(data), encoding="utf-8"
    )


def test_valid_current_manifest(tmp_path: Path) -> None:
    write_manifest(tmp_path, manifest(tmp_path, "run-current"))
    count, errors = validator.load_and_validate(root=tmp_path)
    assert count == 1
    assert errors == []


def test_require_nonempty_rejects_zero_scan(tmp_path: Path) -> None:
    count, errors = validator.load_and_validate(
        root=tmp_path, require_nonempty=True
    )
    assert count == 0
    assert errors == ["run-manifests: no manifest files found"]


def test_hash_mismatch_is_fatal(tmp_path: Path) -> None:
    data = manifest(tmp_path, "run-bad-hash")
    data["outputs"][0]["sha256"] = "0" * 64
    write_manifest(tmp_path, data)
    _, errors = validator.load_and_validate(root=tmp_path)
    assert any("outputs[0].sha256: mismatch" in error for error in errors)


def test_path_escape_is_fatal(tmp_path: Path) -> None:
    data = manifest(tmp_path, "run-escape")
    data["script"]["path"] = "../outside.py"
    write_manifest(tmp_path, data)
    _, errors = validator.load_and_validate(root=tmp_path)
    assert any("script.path: path escapes the repository" in error for error in errors)


def test_quarantine_requires_reason(tmp_path: Path) -> None:
    write_manifest(tmp_path, manifest(tmp_path, "run-quarantine", "quarantined"))
    _, errors = validator.load_and_validate(root=tmp_path)
    assert any("quarantine_reason" in error for error in errors)


def test_supersession_must_be_reciprocal(tmp_path: Path) -> None:
    old = manifest(tmp_path, "run-old", "superseded")
    old["superseded_by"] = "run-new"
    new = manifest(tmp_path, "run-new")
    write_manifest(tmp_path, old)
    write_manifest(tmp_path, new)
    _, errors = validator.load_and_validate(root=tmp_path)
    assert any("successor run-new does not list run-old" in error for error in errors)


def test_valid_supersession_pair(tmp_path: Path) -> None:
    old = manifest(tmp_path, "run-old", "superseded")
    old["superseded_by"] = "run-new"
    new = manifest(tmp_path, "run-new")
    new["supersedes"] = ["run-old"]
    write_manifest(tmp_path, old)
    write_manifest(tmp_path, new)
    count, errors = validator.load_and_validate(root=tmp_path)
    assert count == 2
    assert errors == []
