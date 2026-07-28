"""Bootstrap and validate the frozen legacy run-record archive.

This module repairs a directory-role error without manufacturing provenance:

* ``run-manifests/`` contains only strict schema-v1 execution manifests;
* structurally invalid or pre-schema JSON records are preserved byte-for-byte
  under ``run-records/legacy/``;
* ``run-records/legacy-index.json`` hashes and classifies every archived JSON;
* ``run-records/historical-artifact-baseline.json`` freezes computational text
  artifacts that predate strict manifest ownership.

The historical baseline is deliberately NOT consumed by
``validate_changed_run_coverage.py``.  Any new or modified transcript/output
still requires a strict run manifest.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_DIR = ROOT / "run-manifests"
RECORD_ROOT = ROOT / "run-records"
LEGACY_DIR = RECORD_ROOT / "legacy"
LEGACY_INDEX = RECORD_ROOT / "legacy-index.json"
ARTIFACT_BASELINE = RECORD_ROOT / "historical-artifact-baseline.json"
LOCAL_STAGING = RECORD_ROOT / "local-staging"
MIGRATION_DATE = "2026-07-29"
COMPUTATIONAL_TEXT = re.compile(
    r"^scripts/.*(?:transcript|output).*\.txt$", re.IGNORECASE
)
ALLOWED_CLASSIFICATIONS = {
    "pre-schema-record",
    "strict-invalid-v1-record",
    "strict-valid-with-archived-supersession-edge",
}


def _load_strict_validator():
    path = ROOT / "scripts" / "validate_run_manifests.py"
    spec = importlib.util.spec_from_file_location("strict_run_manifest_validator", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


STRICT = _load_strict_validator()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_lf(path: Path) -> str:
    """Hash bytes after CRLF-to-LF normalization, using bounded memory."""

    digest = hashlib.sha256()
    carry = b""
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            data = carry + chunk
            if data.endswith(b"\r"):
                carry = b"\r"
                data = data[:-1]
            else:
                carry = b""
            digest.update(data.replace(b"\r\n", b"\n"))
    if carry:
        digest.update(carry)
    return digest.hexdigest()


def size_lf(path: Path) -> int:
    """Return byte size after CRLF-to-LF normalization."""

    size = 0
    carry = b""
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            data = carry + chunk
            if data.endswith(b"\r"):
                carry = b"\r"
                data = data[:-1]
            else:
                carry = b""
            normalized = data.replace(b"\r\n", b"\n")
            size += len(normalized)
    return size + len(carry)


def matches_eol_bound(path: Path, raw_digest: str, lf_digest: str) -> bool:
    """Accept only the recorded raw bytes or their CRLF-to-LF form."""

    return sha256(path) == raw_digest or sha256_lf(path) == lf_digest


def _json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


@lru_cache(maxsize=1)
def _indexed_legacy_records() -> dict[str, dict[str, Any]]:
    """Return frozen records keyed by their original basename.

    The index is checked at the point of use.  A specialized domain validator
    may consume a frozen record, but it never becomes a strict execution
    manifest merely because it is readable here.
    """

    index = _json(LEGACY_INDEX)
    rows = index.get("records") if isinstance(index, dict) else None
    if not isinstance(rows, list):
        raise RuntimeError("legacy-index.json: records must be an array")
    result: dict[str, dict[str, Any]] = {}
    for position, row in enumerate(rows):
        if not isinstance(row, dict):
            raise RuntimeError(
                f"legacy-index.records[{position}]: expected an object"
            )
        original = row.get("original_path")
        archived = row.get("archived_path")
        digest = row.get("sha256")
        digest_lf = row.get("sha256_lf")
        if (
            not isinstance(original, str)
            or not original.startswith("run-manifests/")
            or not isinstance(archived, str)
            or not isinstance(digest, str)
            or not isinstance(digest_lf, str)
        ):
            raise RuntimeError(
                f"legacy-index.records[{position}]: incomplete locator"
            )
        name = Path(original).name
        if name in result:
            raise RuntimeError(f"legacy-index.json: duplicate record {name}")
        path = ROOT / archived
        if not path.is_file() or not matches_eol_bound(path, digest, digest_lf):
            raise RuntimeError(f"frozen record fails index binding: {name}")
        result[name] = row
    return result


def frozen_record_path(name: str) -> Path:
    """Resolve one byte-bound frozen record for a specialized validator."""

    if Path(name).name != name:
        raise ValueError("frozen record name must be a basename")
    row = _indexed_legacy_records().get(name)
    if row is None:
        raise FileNotFoundError(f"frozen run record is not indexed: {name}")
    return ROOT / row["archived_path"]


def iter_auditable_run_records(pattern: str) -> list[tuple[str, Path]]:
    """Return strict and frozen records with their original logical paths.

    This is intentionally separate from strict-manifest validation and from
    changed-artifact coverage.  Callers are responsible for applying a
    domain-specific validator to every returned record.
    """

    records: dict[str, Path] = {
        path.name: path for path in MANIFEST_DIR.glob(pattern)
    }
    for name, row in _indexed_legacy_records().items():
        if fnmatch.fnmatchcase(name, pattern):
            if name in records:
                raise RuntimeError(f"duplicate strict/frozen run record: {name}")
            records[name] = ROOT / row["archived_path"]
    return [
        (f"run-manifests/{name}", records[name])
        for name in sorted(records)
    ]


def _write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def _git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout.strip()


def _strict_local_errors(path: Path, data: Any) -> list[str]:
    _, errors = STRICT.validate_manifest(data, path, ROOT)
    prefix = f"{path.relative_to(ROOT).as_posix()}: "
    normalized: list[str] = []
    for error in errors:
        if error.startswith(prefix):
            error = error[len(prefix) :]
        error = re.sub(
            r"\(recorded [0-9a-fA-F]+, actual [0-9a-fA-F]+\)",
            "(recorded/actual hash mismatch)",
            error,
        )
        normalized.append(error)
    return sorted(set(normalized))


def _supersession_refs(data: Any) -> set[str]:
    if not isinstance(data, dict):
        return set()
    refs = {
        item
        for item in data.get("supersedes", [])
        if isinstance(item, str) and item
    }
    successor = data.get("superseded_by")
    if isinstance(successor, str) and successor:
        refs.add(successor)
    return refs


def classify_manifest_directory() -> tuple[
    dict[str, Any], dict[str, list[str]], set[str]
]:
    records: dict[str, Any] = {}
    local_errors: dict[str, list[str]] = {}
    for path in sorted(MANIFEST_DIR.glob("*.json")):
        data = _json(path)
        records[path.name] = data
        local_errors[path.name] = _strict_local_errors(path, data)

    archive = {name for name, errors in local_errors.items() if errors}
    run_id_to_name = {
        data.get("run_id"): name
        for name, data in records.items()
        if isinstance(data, dict) and isinstance(data.get("run_id"), str)
    }

    # Preserve supersession graphs as a unit.  A strict-valid record cannot
    # remain active if one of its declared predecessor/successor records is
    # archived outside the strict manifest set.
    changed = True
    while changed:
        changed = False
        archived_ids = {
            records[name].get("run_id")
            for name in archive
            if isinstance(records[name], dict)
        }
        for name, data in records.items():
            if name in archive:
                continue
            refs = _supersession_refs(data)
            if refs & archived_ids:
                archive.add(name)
                changed = True
        # Also close in the reverse direction for references from an archived
        # record to a strict-valid record.
        for name in list(archive):
            for ref in _supersession_refs(records[name]):
                target = run_id_to_name.get(ref)
                if target is not None and target not in archive:
                    archive.add(target)
                    changed = True

    return records, local_errors, archive


def _classification(data: Any, errors: list[str]) -> str:
    if errors:
        if isinstance(data, dict) and data.get("schema_version") == 1:
            return "strict-invalid-v1-record"
        return "pre-schema-record"
    return "strict-valid-with-archived-supersession-edge"


def _strings(value: Any) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for item in value.values():
            yield from _strings(item)
    elif isinstance(value, list):
        for item in value:
            yield from _strings(item)


def _strict_output_paths() -> set[str]:
    outputs: set[str] = set()
    for path in sorted(MANIFEST_DIR.glob("*.json")):
        data = _json(path)
        artifacts = data.get("outputs") if isinstance(data, dict) else None
        if not isinstance(artifacts, list):
            continue
        for artifact in artifacts:
            if isinstance(artifact, dict) and isinstance(artifact.get("path"), str):
                outputs.add(artifact["path"].replace("\\", "/"))
    return outputs


def _computational_paths() -> set[str]:
    paths: set[str] = set()
    for path in ROOT.glob("scripts/**/*.txt"):
        relative = path.relative_to(ROOT).as_posix()
        if COMPUTATIONAL_TEXT.fullmatch(relative):
            paths.add(relative)
    return paths


def _legacy_references() -> dict[str, list[str]]:
    references: dict[str, list[str]] = defaultdict(list)
    for path in sorted(LEGACY_DIR.glob("*.json")):
        data = _json(path)
        for text in set(_strings(data)):
            normalized = text.replace("\\", "/")
            candidate = ROOT / normalized
            if (
                normalized.startswith("scripts/")
                and normalized.endswith(".txt")
                and candidate.is_file()
            ):
                references[normalized].append(path.name)
    return {key: sorted(value) for key, value in references.items()}


def build_artifact_baseline(source_commit: str) -> dict[str, Any]:
    strict_outputs = _strict_output_paths()
    paths = sorted(_computational_paths() - strict_outputs)
    references = _legacy_references()
    artifacts = []
    for relative in paths:
        path = ROOT / relative
        refs = references.get(relative, [])
        artifacts.append(
            {
                "classification": (
                    "legacy-record-linked" if refs else "historical-unmanifested"
                ),
                "legacy_record_refs": refs,
                "path": relative,
                "sha256": sha256(path),
                "sha256_lf": sha256_lf(path),
                "size_bytes": path.stat().st_size,
                "size_bytes_lf": size_lf(path),
            }
        )
    return {
        "schema_version": 1,
        "migration_date": MIGRATION_DATE,
        "source_main_commit": source_commit,
        "policy": (
            "Frozen pre-guard inventory only. Entries are not execution "
            "manifests and never satisfy changed-artifact coverage."
        ),
        "artifact_count": len(artifacts),
        "artifacts": artifacts,
    }


def bootstrap() -> None:
    if LEGACY_DIR.exists() or LEGACY_INDEX.exists() or ARTIFACT_BASELINE.exists():
        raise RuntimeError("run-record archive already exists; bootstrap is one-shot")
    source_commit = _git("rev-parse", "HEAD")
    records, local_errors, archive = classify_manifest_directory()
    if not archive:
        raise RuntimeError("no legacy records found; refusing empty bootstrap")

    LEGACY_DIR.mkdir(parents=True)
    entries = []
    for name in sorted(archive):
        source = MANIFEST_DIR / name
        destination = LEGACY_DIR / name
        data = records[name]
        errors = local_errors[name]
        source.replace(destination)
        entries.append(
            {
                "archived_path": destination.relative_to(ROOT).as_posix(),
                "classification": _classification(data, errors),
                "original_path": source.relative_to(ROOT).as_posix(),
                "original_schema_version": (
                    data.get("schema_version") if isinstance(data, dict) else None
                ),
                "original_status": (
                    data.get("status") if isinstance(data, dict) else None
                ),
                "sha256": sha256(destination),
                "sha256_lf": sha256_lf(destination),
                "strict_error_count_at_migration": len(errors),
                "strict_errors_at_migration": errors,
            }
        )

    index = {
        "schema_version": 1,
        "migration_date": MIGRATION_DATE,
        "source_main_commit": source_commit,
        "policy": (
            "Byte-preserved historical records; not executable manifests. "
            "They may be consumed only by explicit domain-specific validators "
            "that independently check the referenced evidence."
        ),
        "record_count": len(entries),
        "records": entries,
    }
    _write_json(LEGACY_INDEX, index)

    count, strict_errors = STRICT.load_and_validate(
        root=ROOT, manifest_dir=MANIFEST_DIR, require_nonempty=True
    )
    if strict_errors:
        raise RuntimeError(
            f"strict survivor set is not closed ({count} files):\n"
            + "\n".join(strict_errors)
        )

    _write_json(ARTIFACT_BASELINE, build_artifact_baseline(source_commit))
    errors = validate_archive()
    if errors:
        raise RuntimeError("archive bootstrap validation failed:\n" + "\n".join(errors))
    print(
        "run-record archive bootstrap OK: "
        f"{len(entries)} legacy record(s), {count} strict manifest(s)"
    )


def validate_archive() -> list[str]:
    errors: list[str] = []
    staged = sorted(LOCAL_STAGING.glob("*.json"))
    if staged:
        errors.append(
            "run-records/local-staging: staged JSON must not be committed "
            f"({len(staged)} file(s))"
        )
    if not LEGACY_INDEX.is_file():
        return ["run-records/legacy-index.json is missing"]
    if not ARTIFACT_BASELINE.is_file():
        return ["run-records/historical-artifact-baseline.json is missing"]
    if not LEGACY_DIR.is_dir():
        return ["run-records/legacy/ is missing"]

    try:
        index = _json(LEGACY_INDEX)
        baseline = _json(ARTIFACT_BASELINE)
    except (OSError, json.JSONDecodeError) as exc:
        return [f"archive JSON is unreadable: {exc}"]

    records = index.get("records") if isinstance(index, dict) else None
    if not isinstance(records, list):
        errors.append("legacy-index.json: records must be an array")
        records = []
    if index.get("record_count") != len(records):
        errors.append("legacy-index.json: record_count mismatch")

    indexed_paths: set[str] = set()
    for position, record in enumerate(records):
        label = f"legacy-index.records[{position}]"
        if not isinstance(record, dict):
            errors.append(f"{label}: expected an object")
            continue
        archived = record.get("archived_path")
        original = record.get("original_path")
        classification = record.get("classification")
        digest = record.get("sha256")
        digest_lf = record.get("sha256_lf")
        if not isinstance(archived, str):
            errors.append(f"{label}.archived_path: expected a string")
            continue
        indexed_paths.add(archived)
        path = ROOT / archived
        if not path.is_file():
            errors.append(f"{label}.archived_path: file is missing")
        elif (
            not isinstance(digest, str)
            or not isinstance(digest_lf, str)
            or not matches_eol_bound(path, digest, digest_lf)
        ):
            errors.append(f"{label}.sha256/sha256_lf: mismatch")
        if not isinstance(original, str) or not original.startswith("run-manifests/"):
            errors.append(f"{label}.original_path: invalid")
        elif (ROOT / original).exists():
            errors.append(f"{label}.original_path: still exists in strict directory")
        if classification not in ALLOWED_CLASSIFICATIONS:
            errors.append(f"{label}.classification: invalid")

    disk_paths = {
        path.relative_to(ROOT).as_posix() for path in LEGACY_DIR.glob("*.json")
    }
    if indexed_paths != disk_paths:
        errors.append(
            "legacy-index.json: indexed legacy files do not match the directory"
        )

    count, strict_errors = STRICT.load_and_validate(
        root=ROOT, manifest_dir=MANIFEST_DIR, require_nonempty=True
    )
    if strict_errors:
        errors.append(
            f"strict run-manifest set is invalid ({count} files, "
            f"{len(strict_errors)} errors)"
        )

    artifacts = baseline.get("artifacts") if isinstance(baseline, dict) else None
    if not isinstance(artifacts, list):
        errors.append("historical-artifact-baseline.json: artifacts must be an array")
        artifacts = []
    if baseline.get("artifact_count") != len(artifacts):
        errors.append("historical-artifact-baseline.json: artifact_count mismatch")

    baseline_paths: set[str] = set()
    archived_names = {Path(path).name for path in disk_paths}
    for position, artifact in enumerate(artifacts):
        label = f"historical-artifact-baseline.artifacts[{position}]"
        if not isinstance(artifact, dict):
            errors.append(f"{label}: expected an object")
            continue
        relative = artifact.get("path")
        if not isinstance(relative, str):
            errors.append(f"{label}.path: expected a string")
            continue
        baseline_paths.add(relative)
        path = ROOT / relative
        if not path.is_file():
            errors.append(f"{label}.path: file is missing")
            continue
        raw_digest = artifact.get("sha256")
        lf_digest = artifact.get("sha256_lf")
        if (
            not isinstance(raw_digest, str)
            or not isinstance(lf_digest, str)
            or not matches_eol_bound(path, raw_digest, lf_digest)
        ):
            errors.append(f"{label}.sha256/sha256_lf: mismatch")
        sizes = {artifact.get("size_bytes"), artifact.get("size_bytes_lf")}
        if path.stat().st_size not in sizes:
            errors.append(f"{label}.size_bytes/size_bytes_lf: mismatch")
        refs = artifact.get("legacy_record_refs")
        if not isinstance(refs, list) or any(ref not in archived_names for ref in refs):
            errors.append(f"{label}.legacy_record_refs: invalid")

    expected_baseline = _computational_paths() - _strict_output_paths()
    if baseline_paths != expected_baseline:
        missing = sorted(expected_baseline - baseline_paths)
        extra = sorted(baseline_paths - expected_baseline)
        errors.append(
            "historical-artifact-baseline.json: path set mismatch "
            f"(missing {len(missing)}, extra {len(extra)})"
        )
    return sorted(set(errors))


def upgrade_eol_metadata() -> None:
    """Add portable EOL metadata to a just-bootstrapped Windows archive."""

    index = _json(LEGACY_INDEX)
    records = index.get("records") if isinstance(index, dict) else None
    if not isinstance(records, list):
        raise RuntimeError("legacy-index.json: records must be an array")
    for position, record in enumerate(records):
        if not isinstance(record, dict):
            raise RuntimeError(
                f"legacy-index.records[{position}]: expected an object"
            )
        path = ROOT / str(record.get("archived_path", ""))
        recorded = record.get("sha256")
        if not path.is_file() or sha256(path) != recorded:
            raise RuntimeError(
                f"legacy-index.records[{position}]: raw migration hash mismatch"
            )
        record["sha256_lf"] = sha256_lf(path)
    _write_json(LEGACY_INDEX, index)

    baseline = _json(ARTIFACT_BASELINE)
    artifacts = baseline.get("artifacts") if isinstance(baseline, dict) else None
    if not isinstance(artifacts, list):
        raise RuntimeError(
            "historical-artifact-baseline.json: artifacts must be an array"
        )
    for position, artifact in enumerate(artifacts):
        if not isinstance(artifact, dict):
            raise RuntimeError(
                f"historical-artifact-baseline.artifacts[{position}]: "
                "expected an object"
            )
        path = ROOT / str(artifact.get("path", ""))
        if (
            not path.is_file()
            or sha256(path) != artifact.get("sha256")
            or sha256_lf(path) != artifact.get("sha256_lf")
        ):
            raise RuntimeError(
                f"historical-artifact-baseline.artifacts[{position}]: "
                "migration hash mismatch"
            )
        artifact["size_bytes_lf"] = size_lf(path)
    _write_json(ARTIFACT_BASELINE, baseline)

    _indexed_legacy_records.cache_clear()
    errors = validate_archive()
    if errors:
        raise RuntimeError("EOL index upgrade failed:\n" + "\n".join(errors))
    print(
        "run-record archive EOL metadata upgraded: "
        f"{len(records)} record(s), {len(artifacts)} artifact(s)"
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", choices=("bootstrap", "check", "upgrade-index-eol")
    )
    args = parser.parse_args(argv)
    if args.command == "bootstrap":
        try:
            bootstrap()
        except (OSError, RuntimeError, json.JSONDecodeError) as exc:
            print(f"run-record archive bootstrap failed: {exc}")
            return 1
        return 0
    if args.command == "upgrade-index-eol":
        try:
            upgrade_eol_metadata()
        except (OSError, RuntimeError, json.JSONDecodeError) as exc:
            print(f"run-record archive EOL index upgrade failed: {exc}")
            return 1
        return 0

    errors = validate_archive()
    if errors:
        print(f"run-record archive validation failed: {len(errors)} problem(s)")
        for error in errors:
            print(f"  - {error}")
        return 1
    index = _json(LEGACY_INDEX)
    baseline = _json(ARTIFACT_BASELINE)
    print(
        "run-record archive validation OK: "
        f"{index['record_count']} legacy record(s), "
        f"{baseline['artifact_count']} frozen historical artifact(s)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
