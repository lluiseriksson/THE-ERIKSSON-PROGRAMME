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


def test_finished_time_cannot_precede_start(tmp_path: Path) -> None:
    data = manifest(tmp_path, "run-time-reversed")
    data["finished_utc"] = "2026-07-11T17:59:00Z"
    write_manifest(tmp_path, data)
    _, errors = validator.load_and_validate(root=tmp_path)
    assert any("must not precede started_utc" in error for error in errors)


def test_command_must_name_hashed_script(tmp_path: Path) -> None:
    data = manifest(tmp_path, "run-command-mismatch")
    data["command"] = ["python", "scripts/another.py"]
    write_manifest(tmp_path, data)
    _, errors = validator.load_and_validate(root=tmp_path)
    assert any("must include the recorded script.path" in error for error in errors)


def test_command_script_can_be_relative_to_recorded_working_directory(
    tmp_path: Path,
) -> None:
    data = manifest(tmp_path, "run-relative-command")
    data["working_directory"] = "scripts"
    data["command"] = ["python", "run.py"]
    write_manifest(tmp_path, data)
    _, errors = validator.load_and_validate(root=tmp_path)
    assert errors == []


def test_working_directory_must_exist(tmp_path: Path) -> None:
    data = manifest(tmp_path, "run-missing-cwd")
    data["working_directory"] = "missing-directory"
    write_manifest(tmp_path, data)
    _, errors = validator.load_and_validate(root=tmp_path)
    assert any("working_directory: directory does not exist" in error for error in errors)


def test_output_path_has_one_manifest_owner(tmp_path: Path) -> None:
    first = manifest(tmp_path, "run-owner-one")
    second = manifest(tmp_path, "run-owner-two")
    second["outputs"] = first["outputs"]
    write_manifest(tmp_path, first)
    write_manifest(tmp_path, second)
    _, errors = validator.load_and_validate(root=tmp_path)
    assert any("is already owned by run" in error for error in errors)


def test_lf_hash_makes_recorded_crlf_run_portable(tmp_path: Path) -> None:
    data = manifest(tmp_path, "run-portable-eol")
    script = tmp_path / data["script"]["path"]
    output = tmp_path / data["outputs"][0]["path"]
    script.write_bytes(b"print('run')\r\n")
    output.write_bytes(b"evidence\r\n")
    data["script"]["sha256"] = digest(script)
    data["script"]["sha256_lf"] = validator.file_sha256_lf(script)
    data["outputs"][0]["sha256"] = digest(output)
    data["outputs"][0]["sha256_lf"] = validator.file_sha256_lf(output)
    write_manifest(tmp_path, data)
    script.write_bytes(script.read_bytes().replace(b"\r\n", b"\n"))
    output.write_bytes(output.read_bytes().replace(b"\r\n", b"\n"))
    _, errors = validator.load_and_validate(root=tmp_path)
    assert errors == []
