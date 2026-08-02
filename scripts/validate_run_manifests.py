"""Validate reproducible execution manifests.

The manifest layer is deliberately independent of the Surface Theorem scripts.
It records immutable evidence about a run; it never promotes a mathematical
claim or rewrites an artifact.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import hashlib
import json
import os
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_DIR = ROOT / "run-manifests"
# Hexadecimal case is presentation-only; digest comparison remains byte-exact.
# Accepting uppercase here permits manifests captured from Windows tooling while
# preserving the same 256-bit value and the dual LF/CRLF policy.
SHA256 = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
RUN_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
STATUSES = {"current", "superseded", "quarantined"}
BASELINE_SCHEMA_VERSION = 1
RESULT_SCHEMA_VERSION = 1
ACTUAL_DIGEST = re.compile(r"(, actual )[0-9a-fA-F]{64}(\))")


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


def file_sha256_eol_variants(path: Path) -> set[str]:
    """Return hashes for the checked-out bytes and both text EOL forms.

    Git may materialize a tracked text artifact with LF or CRLF depending on
    checkout policy.  The historical digest is preserved; accepting either
    line-ending representation avoids making validation depend on the runner
    OS.  No other byte transformation is accepted.
    """

    data = path.read_bytes()
    lf = data.replace(b"\r\n", b"\n")
    crlf = lf.replace(b"\n", b"\r\n")
    return {
        hashlib.sha256(candidate).hexdigest()
        for candidate in (data, lf, crlf)
    }


def _exists_with_exact_case(root: Path, path: Path, *, directory: bool) -> bool:
    """Apply Linux path-case semantics on every supported runner OS."""

    try:
        relative = path.relative_to(root.resolve())
    except ValueError:
        return False
    cursor = root.resolve()
    for part in relative.parts:
        try:
            names = _directory_entry_names(cursor)
        except OSError:
            return False
        if part not in names:
            return False
        cursor = cursor / part
    return cursor.is_dir() if directory else cursor.is_file()


@lru_cache(maxsize=None)
def _directory_entry_names(directory: Path) -> frozenset[str]:
    return frozenset(entry.name for entry in directory.iterdir())


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
    # Manifests captured on Windows legitimately contain backslashes.  Treat
    # them as repository separators on every runner instead of as literal
    # filename characters on POSIX.
    candidate = Path(text.replace("\\", "/"))
    if candidate.is_absolute():
        errors.append(f"{field}: path must be repository-relative")
        return None
    normalized = Path(os.path.normpath(root.resolve() / candidate))
    resolved = normalized.resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError:
        errors.append(f"{field}: path escapes the repository")
        return None
    return normalized


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
    *,
    check_hash: bool = True,
) -> None:
    if not isinstance(artifact, dict):
        errors.append(f"{field}: expected an object")
        return
    path = _repo_path(root, artifact.get("path"), f"{field}.path", errors)
    digest = artifact.get("sha256")
    if not isinstance(digest, str) or not SHA256.fullmatch(digest):
        errors.append(f"{field}.sha256: expected a 64-digit SHA-256 digest")
    portable_digest = artifact.get("sha256_lf")
    if portable_digest is not None and (
        not isinstance(portable_digest, str) or not SHA256.fullmatch(portable_digest)
    ):
        errors.append(f"{field}.sha256_lf: expected a 64-digit SHA-256 digest")
    if path is None:
        return
    if not _exists_with_exact_case(root, path, directory=False):
        errors.append(f"{field}.path: file does not exist")
        return
    # A superseded/quarantined run is retained as a historical record.  Its
    # paths and digest fields remain structurally checked, but its inputs may
    # legitimately have been replaced by a later worktree.  Current runs alone
    # carry an active reproducibility claim and therefore require byte hashes.
    if not check_hash:
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
        if digest.lower() not in file_sha256_eol_variants(path):
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
    if working_directory is not None and not _exists_with_exact_case(
        root, working_directory, directory=True
    ):
        errors.append("working_directory: directory does not exist")

    script = data.get("script")
    if not isinstance(script, dict):
        errors.append("script: expected an object")
    else:
        _artifact(root, script, "script", errors, check_hash=status == "current")
        script_path = script.get("path")
        if isinstance(script_path, str) and isinstance(command, list):
            normalized_command = [
                part.replace("\\", "/") for part in command if isinstance(part, str)
            ]
            direct_match = script_path.replace("\\", "/") in normalized_command
            cwd_match = False
            if working_directory is not None:
                script_absolute = (root / script_path).resolve()
                for part in command:
                    if not isinstance(part, str):
                        continue
                    candidate = Path(part)
                    if candidate.is_absolute():
                        continue
                    if (working_directory / candidate).resolve() == script_absolute:
                        cwd_match = True
                        break
            if not direct_match and not cwd_match:
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
            _artifact(
                root,
                artifact,
                f"{collection_name}[{index}]",
                errors,
                check_hash=status == "current",
            )

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
    _directory_entry_names.cache_clear()
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


def violation_key(detail: str) -> str:
    """Remove only runner-computed data from a validation error."""

    return ACTUAL_DIGEST.sub(r"\1<computed>\2", detail)


def group_violations(
    errors: list[str],
) -> tuple[dict[str, Counter[str]], Counter[str]]:
    """Group strict-validator output without weakening any validation rule."""

    manifests: dict[str, Counter[str]] = defaultdict(Counter)
    global_errors: Counter[str] = Counter()
    for error in errors:
        match = re.match(r"^(run-manifests/[^:]+\.json): (.*)$", error)
        if match is None:
            global_errors[violation_key(error)] += 1
            continue
        label, detail = match.groups()
        manifests[label][violation_key(detail)] += 1
    return dict(manifests), global_errors


def _published_identity(data: Any) -> dict[str, Any]:
    if not isinstance(data, dict):
        return {"run_id": None, "official_scope_field": None, "official_scope": None}
    if "claim_scope" in data:
        scope_field = "claim_scope"
    elif "scope" in data:
        scope_field = "scope"
    else:
        scope_field = None
    return {
        "run_id": data.get("run_id"),
        "official_scope_field": scope_field,
        "official_scope": data.get(scope_field) if scope_field is not None else None,
    }


def build_debt_baseline(
    *,
    root: Path,
    manifest_dir: Path,
    base_sha: str,
) -> dict[str, Any]:
    """Describe existing strict-validator debt and immutable publication identity."""

    count, errors = load_and_validate(
        root=root, manifest_dir=manifest_dir, require_nonempty=True
    )
    grouped, global_errors = group_violations(errors)
    manifests: dict[str, Any] = {}
    for path in sorted(manifest_dir.glob("*.json")):
        label = path.relative_to(root).as_posix()
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            data = None
        manifests[label] = {
            **_published_identity(data),
            "violations": dict(sorted(grouped.get(label, Counter()).items())),
        }
    return {
        "schema_version": BASELINE_SCHEMA_VERSION,
        "guard": "run-manifest-structure-and-historical-debt-delta",
        "base_sha": base_sha,
        "manifest_count": count,
        "strict_error_count": len(errors),
        "global_violations": dict(sorted(global_errors.items())),
        "manifests": manifests,
    }


def _load_baseline(path: Path) -> dict[str, Any]:
    try:
        baseline = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot load debt baseline {path}: {exc}") from exc
    if not isinstance(baseline, dict):
        raise ValueError("debt baseline: expected a JSON object")
    if baseline.get("schema_version") != BASELINE_SCHEMA_VERSION:
        raise ValueError(
            f"debt baseline: expected schema_version {BASELINE_SCHEMA_VERSION}"
        )
    if baseline.get("guard") != "run-manifest-structure-and-historical-debt-delta":
        raise ValueError("debt baseline: guard identity does not match")
    if not isinstance(baseline.get("base_sha"), str) or not re.fullmatch(
        r"[0-9a-f]{40}", baseline["base_sha"]
    ):
        raise ValueError("debt baseline: base_sha must be a lowercase Git SHA")
    if not isinstance(baseline.get("manifests"), dict):
        raise ValueError("debt baseline: manifests must be an object")
    if not isinstance(baseline.get("global_violations"), dict):
        raise ValueError("debt baseline: global_violations must be an object")
    if baseline.get("manifest_count") != len(baseline["manifests"]):
        raise ValueError("debt baseline: manifest_count does not match manifests")
    violation_total = sum(
        _counter(record.get("violations"), f"manifests.{label}.violations").total()
        for label, record in baseline["manifests"].items()
        if isinstance(record, dict)
    )
    if any(not isinstance(record, dict) for record in baseline["manifests"].values()):
        raise ValueError("debt baseline: every manifest record must be an object")
    violation_total += _counter(
        baseline["global_violations"], "global_violations"
    ).total()
    if baseline.get("strict_error_count") != violation_total:
        raise ValueError("debt baseline: strict_error_count does not match violations")
    return baseline


def _counter(value: Any, field: str) -> Counter[str]:
    if not isinstance(value, dict):
        raise ValueError(f"debt baseline: {field} must be an object")
    result: Counter[str] = Counter()
    for key, count in value.items():
        if not isinstance(key, str) or not isinstance(count, int) or count < 0:
            raise ValueError(
                f"debt baseline: {field} must map strings to non-negative integers"
            )
        result[key] = count
    return result


def error_class(detail: str) -> str:
    """Return an aggregate class while retaining exact keys in the baseline."""

    result = re.sub(r"\[\d+\]", "[*]", detail)
    result = re.sub(r"\(recorded [0-9a-fA-F]{64}, actual <computed>\)", "(digest mismatch)", result)
    result = re.sub(r"output .* is already owned by run .*", "output path is already owned", result)
    result = re.sub(r"supersedes unknown run .*", "supersedes unknown run", result)
    result = re.sub(
        r"superseded run .* does not point back to .*",
        "superseded run does not point back",
        result,
    )
    result = re.sub(
        r"superseded run .* is not marked superseded",
        "superseded run is not marked superseded",
        result,
    )
    return result


def evaluate_debt_guard(
    *,
    root: Path,
    manifest_dir: Path,
    baseline_path: Path,
    require_nonempty: bool,
) -> dict[str, Any]:
    """Accept only new valid manifests and non-increasing inherited debt."""

    baseline = _load_baseline(baseline_path)
    count, strict_errors = load_and_validate(
        root=root,
        manifest_dir=manifest_dir,
        require_nonempty=require_nonempty,
    )
    current, current_global = group_violations(strict_errors)
    baseline_manifests = baseline["manifests"]
    guard_errors: list[str] = []

    current_paths = {
        path.relative_to(root).as_posix(): path
        for path in sorted(manifest_dir.glob("*.json"))
    }
    for label, recorded in sorted(baseline_manifests.items()):
        if not isinstance(recorded, dict):
            raise ValueError(f"debt baseline: manifests.{label} must be an object")
        path = current_paths.get(label)
        if path is None:
            guard_errors.append(f"{label}: protected publication was deleted")
            continue
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            data = None
        expected_identity = {
            "run_id": recorded.get("run_id"),
            "official_scope_field": recorded.get("official_scope_field"),
            "official_scope": recorded.get("official_scope"),
        }
        if _published_identity(data) != expected_identity:
            guard_errors.append(
                f"{label}: protected run_id or official scope/title changed"
            )

        allowed = _counter(
            recorded.get("violations"), f"manifests.{label}.violations"
        )
        observed = current.get(label, Counter())
        for violation, observed_count in sorted(observed.items()):
            allowed_count = allowed[violation]
            if observed_count > allowed_count:
                guard_errors.append(
                    f"{label}: debt increased for {violation} "
                    f"(baseline {allowed_count}, current {observed_count})"
                )

    for label in sorted(set(current_paths) - set(baseline_manifests)):
        for violation, observed_count in sorted(current.get(label, Counter()).items()):
            guard_errors.append(
                f"{label}: new manifest is invalid: {violation} "
                f"(current {observed_count})"
            )

    allowed_global = _counter(
        baseline.get("global_violations"), "global_violations"
    )
    for violation, observed_count in sorted(current_global.items()):
        if observed_count > allowed_global[violation]:
            guard_errors.append(
                f"global debt increased for {violation} "
                f"(baseline {allowed_global[violation]}, current {observed_count})"
            )

    debt_by_class: Counter[str] = Counter()
    for violations in current.values():
        for detail, occurrence_count in violations.items():
            debt_by_class[error_class(detail)] += occurrence_count
    for detail, occurrence_count in current_global.items():
        debt_by_class[error_class(detail)] += occurrence_count

    return {
        "guard": baseline["guard"],
        "baseline_sha": baseline["base_sha"],
        "manifest_count": count,
        "strict_error_count": len(strict_errors),
        "invalid_manifest_count": sum(1 for value in current.values() if value),
        "debt_by_class": dict(sorted(debt_by_class.items())),
        "guard_errors": sorted(set(guard_errors)),
    }


def _write_result(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def _result_payload(
    *, status: str, exit_code: int, first_cause: str | None, report: dict[str, Any] | None
) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema_version": RESULT_SCHEMA_VERSION,
        "status": status,
        "exit_code": exit_code,
        "first_cause": first_cause,
    }
    if report is not None:
        payload["report"] = {key: value for key, value in report.items() if key != "guard_errors"}
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--require-nonempty",
        action="store_true",
        help="fail if the repository has not committed any manifests yet",
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        help="apply the versioned historical-debt delta guard",
    )
    parser.add_argument(
        "--result-file",
        type=Path,
        help="write a machine-readable status, exit code, and first cause",
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=ROOT,
        help=argparse.SUPPRESS,
    )
    args = parser.parse_args(argv)
    root = args.root.resolve()
    manifest_dir = root / "run-manifests"
    result_file = args.result_file
    if result_file is not None and not result_file.is_absolute():
        result_file = root / result_file
    if result_file is not None:
        _write_result(
            result_file,
            _result_payload(
                status="RUNNING",
                exit_code=2,
                first_cause="validation did not complete",
                report=None,
            ),
        )

    if args.baseline is not None:
        baseline_path = args.baseline
        if not baseline_path.is_absolute():
            baseline_path = root / baseline_path
        try:
            report = evaluate_debt_guard(
                root=root,
                manifest_dir=manifest_dir,
                baseline_path=baseline_path,
                require_nonempty=args.require_nonempty,
            )
        except (OSError, ValueError) as exc:
            first_cause = str(exc)
            print(f"run-manifest structure/debt-delta guard ERROR: {first_cause}")
            if result_file is not None:
                _write_result(
                    result_file,
                    _result_payload(
                        status="FAIL",
                        exit_code=2,
                        first_cause=first_cause,
                        report=None,
                    ),
                )
            return 2
        guard_errors = report["guard_errors"]
        for rule, rule_count in report["debt_by_class"].items():
            print(f"DEBT: {rule_count:4d}  {rule}")
        if guard_errors:
            for error in guard_errors:
                print(f"ERROR: {error}")
            first_cause = guard_errors[0]
            print(
                "run-manifest structure/debt-delta guard failed: "
                f"{report['manifest_count']} file(s), "
                f"{report['strict_error_count']} inherited/current strict error(s), "
                f"{len(guard_errors)} guard error(s)"
            )
            if result_file is not None:
                _write_result(
                    result_file,
                    _result_payload(
                        status="FAIL",
                        exit_code=1,
                        first_cause=first_cause,
                        report=report,
                    ),
                )
            return 1
        print(
            "run-manifest structure/debt-delta guard PASS: "
            f"{report['manifest_count']} file(s), "
            f"{report['strict_error_count']} visible inherited strict error(s), "
            "no new debt"
        )
        if result_file is not None:
            _write_result(
                result_file,
                _result_payload(
                    status="PASS", exit_code=0, first_cause=None, report=report
                ),
            )
        return 0

    count, errors = load_and_validate(
        root=root,
        manifest_dir=manifest_dir,
        require_nonempty=args.require_nonempty,
    )
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        print(f"run manifest validation failed: {count} file(s), {len(errors)} error(s)")
        if result_file is not None:
            _write_result(
                result_file,
                _result_payload(
                    status="FAIL",
                    exit_code=1,
                    first_cause=errors[0],
                    report={
                        "manifest_count": count,
                        "strict_error_count": len(errors),
                    },
                ),
            )
        return 1
    print(f"run manifest validation OK: {count} file(s)")
    if count == 0:
        print("bootstrap state: no manifests committed; use --require-nonempty to forbid")
    if result_file is not None:
        _write_result(
            result_file,
            _result_payload(
                status="PASS",
                exit_code=0,
                first_cause=None,
                report={"manifest_count": count, "strict_error_count": 0},
            ),
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
