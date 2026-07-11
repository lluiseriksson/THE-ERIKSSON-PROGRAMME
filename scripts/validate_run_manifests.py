"""Validate reproducible execution manifests.

The manifest layer is deliberately independent of the Surface Theorem scripts.
It records immutable evidence about a run; it never promotes a mathematical
claim or rewrites an artifact.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_DIR = ROOT / "run-manifests"
SHA256 = re.compile(r"^[0-9a-f]{64}$")
RUN_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
STATUSES = {"current", "superseded", "quarantined"}


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def file_sha256_lf(path: Path) -> str:
    digest = hashlib.sha256()
    digest.update(path.read_bytes().replace(b"\r\n", b"\n"))
    return digest.hexdigest()


def _string(value: Any, field: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{field}: expected a non-empty string")
        return None
    return value


def _repo_path(
    root: Path, value: Any, field: str, errors: list[str]
) -> Path | None:
    text = _string(value, field, errors)
    if text is None:
        return None
    candidate = Path(text)
    if candidate.is_absolute():
        errors.append(f"{field}: path must be repository-relative")
        return None
    resolved = (root / candidate).resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError:
        errors.append(f"{field}: path escapes the repository")
        return None
    return resolved


def _timestamp(value: Any, field: str, errors: list[str]) -> datetime | None:
    text = _string(value, field, errors)
    if text is None:
        return None
    if not text.endswith("Z"):
        errors.append(f"{field}: timestamp must use UTC and end in Z")
        return None
    try:
        return datetime.fromisoformat(text[:-1] + "+00:00")
    except ValueError:
        errors.append(f"{field}: invalid ISO-8601 timestamp")
        return None


def _artifact(
    root: Path,
    artifact: Any,
    field: str,
    errors: list[str],
) -> None:
    if not isinstance(artifact, dict):
        errors.append(f"{field}: expected an object")
        return
    path = _repo_path(root, artifact.get("path"), f"{field}.path", errors)
    digest = artifact.get("sha256")
    if not isinstance(digest, str) or not SHA256.fullmatch(digest):
        errors.append(f"{field}.sha256: expected a lowercase SHA-256 digest")
    portable_digest = artifact.get("sha256_lf")
    if portable_digest is not None and (
        not isinstance(portable_digest, str) or not SHA256.fullmatch(portable_digest)
    ):
        errors.append(f"{field}.sha256_lf: expected a lowercase SHA-256 digest")
    if path is None:
        return
    if not path.is_file():
        errors.append(f"{field}.path: file does not exist")
        return
    if isinstance(portable_digest, str) and SHA256.fullmatch(portable_digest):
        actual_lf = file_sha256_lf(path)
        if actual_lf != portable_digest:
            errors.append(
                f"{field}.sha256_lf: mismatch (recorded {portable_digest}, "
                f"actual {actual_lf})"
            )
    elif isinstance(digest, str) and SHA256.fullmatch(digest):
        actual = file_sha256(path)
        if actual != digest:
            errors.append(
                f"{field}.sha256: mismatch (recorded {digest}, actual {actual})"
            )


def validate_manifest(
    data: Any,
    source: Path,
    root: Path,
) -> tuple[str | None, list[str]]:
    errors: list[str] = []
    label = source.relative_to(root).as_posix()
    if not isinstance(data, dict):
        return None, [f"{label}: expected a JSON object"]

    if data.get("schema_version") != 1:
        errors.append("schema_version: expected 1")

    run_id = _string(data.get("run_id"), "run_id", errors)
    if run_id is not None:
        if not RUN_ID.fullmatch(run_id):
            errors.append("run_id: invalid identifier")
        if source.stem != run_id:
            errors.append("run_id: must match the manifest filename")

    _string(data.get("claim_scope"), "claim_scope", errors)
    started = _timestamp(data.get("started_utc"), "started_utc", errors)
    finished = _timestamp(data.get("finished_utc"), "finished_utc", errors)
    if started is not None and finished is not None and finished < started:
        errors.append("finished_utc: must not precede started_utc")

    status = data.get("status")
    if status not in STATUSES:
        errors.append(f"status: expected one of {sorted(STATUSES)}")

    command = data.get("command")
    if (
        not isinstance(command, list)
        or not command
        or any(not isinstance(part, str) or not part for part in command)
    ):
        errors.append("command: expected a non-empty array of non-empty strings")

    working_directory = _repo_path(
        root, data.get("working_directory"), "working_directory", errors
    )
    if working_directory is not None and not working_directory.is_dir():
        errors.append("working_directory: directory does not exist")

    script = data.get("script")
    if not isinstance(script, dict):
        errors.append("script: expected an object")
    else:
        _artifact(root, script, "script", errors)
        script_path = script.get("path")
        if isinstance(script_path, str) and isinstance(command, list):
            normalized_command = [
                part.replace("\\", "/") for part in command if isinstance(part, str)
            ]
            if script_path.replace("\\", "/") not in normalized_command:
                errors.append("command: must include the recorded script.path")

    environment = data.get("environment")
    if not isinstance(environment, dict):
        errors.append("environment: expected an object")
    else:
        _string(environment.get("python"), "environment.python", errors)
        libraries = environment.get("libraries")
        if not isinstance(libraries, dict):
            errors.append("environment.libraries: expected an object")
        else:
            for name, version in libraries.items():
                if not isinstance(name, str) or not name:
                    errors.append("environment.libraries: invalid library name")
                if not isinstance(version, str) or not version:
                    errors.append(
                        f"environment.libraries.{name}: expected a version string"
                    )

    for collection_name in ("inputs", "outputs"):
        collection = data.get(collection_name)
        if not isinstance(collection, list):
            errors.append(f"{collection_name}: expected an array")
            continue
        if collection_name == "outputs" and not collection:
            errors.append("outputs: at least one committed output is required")
        for index, artifact in enumerate(collection):
            _artifact(root, artifact, f"{collection_name}[{index}]", errors)

    supersedes = data.get("supersedes")
    if (
        not isinstance(supersedes, list)
        or any(not isinstance(item, str) or not RUN_ID.fullmatch(item) for item in supersedes)
    ):
        errors.append("supersedes: expected an array of run identifiers")

    superseded_by = data.get("superseded_by")
    quarantine_reason = data.get("quarantine_reason")
    if status == "superseded":
        _string(superseded_by, "superseded_by", errors)
    elif superseded_by is not None:
        errors.append("superseded_by: allowed only when status is superseded")

    if status == "quarantined":
        _string(quarantine_reason, "quarantine_reason", errors)
    elif quarantine_reason is not None:
        errors.append("quarantine_reason: allowed only when status is quarantined")

    return run_id, [f"{label}: {error}" for error in errors]


def load_and_validate(
    root: Path = ROOT,
    manifest_dir: Path | None = None,
    require_nonempty: bool = False,
) -> tuple[int, list[str]]:
    directory = manifest_dir or (root / "run-manifests")
    paths = sorted(directory.glob("*.json")) if directory.is_dir() else []
    errors: list[str] = []
    if require_nonempty and not paths:
        return 0, ["run-manifests: no manifest files found"]

    records: dict[str, tuple[dict[str, Any], Path]] = {}
    output_owners: dict[str, str] = {}
    for path in paths:
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            errors.append(f"{path.relative_to(root).as_posix()}: invalid JSON: {exc}")
            continue
        run_id, local_errors = validate_manifest(data, path, root)
        errors.extend(local_errors)
        if run_id is None:
            continue
        if run_id in records:
            errors.append(f"run_id {run_id}: duplicate manifest")
        else:
            records[run_id] = (data, path)
            for artifact in data.get("outputs", []):
                if not isinstance(artifact, dict) or not isinstance(
                    artifact.get("path"), str
                ):
                    continue
                output_path = artifact["path"].replace("\\", "/")
                previous = output_owners.get(output_path)
                if previous is not None:
                    errors.append(
                        f"{path.relative_to(root).as_posix()}: output {output_path} "
                        f"is already owned by run {previous}"
                    )
                else:
                    output_owners[output_path] = run_id

    for run_id, (data, path) in records.items():
        label = path.relative_to(root).as_posix()
        for old_id in data.get("supersedes", []):
            old = records.get(old_id)
            if old is None:
                errors.append(f"{label}: supersedes unknown run {old_id}")
                continue
            old_data = old[0]
            if old_data.get("status") != "superseded":
                errors.append(f"{label}: superseded run {old_id} is not marked superseded")
            if old_data.get("superseded_by") != run_id:
                errors.append(
                    f"{label}: superseded run {old_id} does not point back to {run_id}"
                )

        successor = data.get("superseded_by")
        if isinstance(successor, str):
            successor_record = records.get(successor)
            if successor_record is None:
                errors.append(f"{label}: superseded_by references unknown run {successor}")
            elif run_id not in successor_record[0].get("supersedes", []):
                errors.append(
                    f"{label}: successor {successor} does not list {run_id} in supersedes"
                )

    for start in records:
        seen: set[str] = set()
        cursor: str | None = start
        while cursor is not None and cursor in records:
            if cursor in seen:
                errors.append(f"run_id {start}: supersession cycle detected")
                break
            seen.add(cursor)
            successor = records[cursor][0].get("superseded_by")
            cursor = successor if isinstance(successor, str) else None

    return len(paths), sorted(set(errors))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--require-nonempty",
        action="store_true",
        help="fail if the repository has not committed any manifests yet",
    )
    args = parser.parse_args(argv)
    count, errors = load_and_validate(require_nonempty=args.require_nonempty)
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        print(f"run manifest validation failed: {count} file(s), {len(errors)} error(s)")
        return 1
    print(f"run manifest validation OK: {count} file(s)")
    if count == 0:
        print("bootstrap state: no manifests committed; use --require-nonempty to forbid")
    return 0


if __name__ == "__main__":
    sys.exit(main())
