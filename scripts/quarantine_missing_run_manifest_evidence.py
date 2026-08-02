"""Quarantine run manifests whose declared script/input evidence is absent.

The migration is intentionally narrow.  Population membership is derived from
exact-case paths tracked by ``HEAD`` and is accepted only at the frozen owner
counts.  Only the top-level ``status`` and ``quarantine_reason`` JSON values may
change; every other parsed value, including every path and digest, is checked
before any file is replaced.

Run without arguments for a read-only plan.  Pass ``--apply`` to write the
validated plan.  The operation is deterministic and idempotent, uses no
decision-making ``assert``, prepares every replacement before the first write,
and rolls back already replaced files if a replacement fails.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import stat
import subprocess
import tempfile
from typing import Any, Iterable


EXPECTED_MANIFESTS = 623
EXPECTED_AFFECTED = 319
EXPECTED_REFERENCES = 688
EXPECTED_BULK_MANIFESTS = 315
EXPECTED_BULK_REFERENCES = 679
EXPECTED_REMAINDER_MANIFESTS = 4
EXPECTED_REMAINDER_REFERENCES = 9
EXPECTED_EXISTING_OUTPUT_REFERENCES = 810

BULK_PREFIX = "surface-scaled-bulk-cwin3p2"
REMAINDER_PREFIX = "surface-remainder"
OWNER_REASON = (
    "Owner decision 2026-08-02 (Lluis Eriksson): quarantined because declared "
    "script/input evidence is unavailable in public refs; paths and digests are "
    "retained as recovery keys."
)
MUTABLE_KEYS = {"status", "quarantine_reason"}


class MigrationError(RuntimeError):
    """A fail-closed migration rejection."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise MigrationError(message)


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise MigrationError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def load_object(raw: bytes, path: Path) -> dict[str, Any]:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise MigrationError(f"{path}: not UTF-8: {exc}") from exc
    try:
        value = json.loads(text, object_pairs_hook=reject_duplicate_keys)
    except (json.JSONDecodeError, MigrationError) as exc:
        raise MigrationError(f"{path}: invalid JSON: {exc}") from exc
    require(isinstance(value, dict), f"{path}: root must be a JSON object")
    return value


def git_output(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        encoding="utf-8",
    )
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip()
        raise MigrationError(f"git {' '.join(args)} failed: {detail}")
    return result.stdout


def tracked_paths(root: Path) -> set[str]:
    return set(git_output(root, "ls-tree", "-r", "--name-only", "HEAD").splitlines())


def normalized_repo_path(value: str) -> str:
    return value.replace("\\", "/")


def declared_evidence(manifest: dict[str, Any]) -> Iterable[tuple[str, str]]:
    script = manifest.get("script")
    if isinstance(script, dict) and isinstance(script.get("path"), str):
        yield "script.path", script["path"]

    inputs = manifest.get("inputs")
    if isinstance(inputs, list):
        for index, entry in enumerate(inputs):
            if isinstance(entry, dict) and isinstance(entry.get("path"), str):
                yield f"inputs[{index}].path", entry["path"]


def nested_paths(value: Any) -> Iterable[str]:
    if isinstance(value, dict):
        path = value.get("path")
        if isinstance(path, str):
            yield path
        for key, child in value.items():
            if key != "path":
                yield from nested_paths(child)
    elif isinstance(value, list):
        for child in value:
            yield from nested_paths(child)


def sensitive_scalars(value: Any, parent_sensitive: bool = False) -> int:
    """Count path/digest scalars for an explicit preservation summary."""

    if isinstance(value, dict):
        count = 0
        for key, child in value.items():
            lower = key.lower()
            sensitive = parent_sensitive or key == "path" or "sha256" in lower or "digest" in lower
            count += sensitive_scalars(child, sensitive)
        return count
    if isinstance(value, list):
        return sum(sensitive_scalars(child, parent_sensitive) for child in value)
    return int(parent_sensitive and isinstance(value, (str, int, float, bool)))


def skip_space(text: str, position: int) -> int:
    while position < len(text) and text[position] in " \t\r\n":
        position += 1
    return position


def top_level_members(text: str, path: Path) -> tuple[dict[str, tuple[int, int]], int]:
    """Return exact value spans for each root member and the last value end."""

    decoder = json.JSONDecoder(object_pairs_hook=reject_duplicate_keys)
    position = skip_space(text, 0)
    require(position < len(text) and text[position] == "{", f"{path}: root is not an object")
    position += 1
    members: dict[str, tuple[int, int]] = {}
    last_value_end = position

    while True:
        position = skip_space(text, position)
        require(position < len(text), f"{path}: unterminated root object")
        if text[position] == "}":
            return members, last_value_end

        try:
            key, key_length = decoder.raw_decode(text[position:])
        except (json.JSONDecodeError, MigrationError) as exc:
            raise MigrationError(f"{path}: cannot locate root key: {exc}") from exc
        require(isinstance(key, str), f"{path}: root key is not a string")
        require(key not in members, f"{path}: duplicate root key {key!r}")
        position += key_length
        position = skip_space(text, position)
        require(position < len(text) and text[position] == ":", f"{path}: missing colon after {key!r}")
        value_start = skip_space(text, position + 1)
        try:
            _, value_length = decoder.raw_decode(text[value_start:])
        except (json.JSONDecodeError, MigrationError) as exc:
            raise MigrationError(f"{path}: cannot locate value for {key!r}: {exc}") from exc
        value_end = value_start + value_length
        members[key] = (value_start, value_end)
        last_value_end = value_end
        position = skip_space(text, value_end)
        require(position < len(text), f"{path}: unterminated root object")
        if text[position] == ",":
            position += 1
            continue
        require(text[position] == "}", f"{path}: expected comma or closing brace")


def replacement_reason(manifest: dict[str, Any]) -> str:
    previous = manifest.get("quarantine_reason")
    if isinstance(previous, str) and previous and not previous.startswith(OWNER_REASON):
        return f"{OWNER_REASON} Prior quarantine reason retained verbatim: {previous}"
    if isinstance(previous, str) and previous.startswith(OWNER_REASON):
        return previous
    return OWNER_REASON


def rewrite_manifest(raw: bytes, path: Path, before: dict[str, Any]) -> bytes:
    text = raw.decode("utf-8")
    members, last_value_end = top_level_members(text, path)
    require("status" in members, f"{path}: missing top-level status")

    reason = replacement_reason(before)
    edits: list[tuple[int, int, str]] = []
    status_start, status_end = members["status"]
    edits.append((status_start, status_end, json.dumps("quarantined")))

    encoded_reason = json.dumps(reason, ensure_ascii=False)
    if "quarantine_reason" in members:
        reason_start, reason_end = members["quarantine_reason"]
        edits.append((reason_start, reason_end, encoded_reason))
    else:
        multiline = "\n" in text or "\r" in text
        eol = "\r\n" if "\r\n" in text else "\n"
        status_line_start = text.rfind("\n", 0, status_start) + 1
        status_prefix = text[status_line_start:status_start]
        indent = status_prefix[: len(status_prefix) - len(status_prefix.lstrip(" \t"))]
        insertion = f",{eol}{indent}\"quarantine_reason\": {encoded_reason}" if multiline else f", \"quarantine_reason\": {encoded_reason}"
        edits.append((last_value_end, last_value_end, insertion))

    for start, end, replacement in sorted(edits, key=lambda item: (item[0], item[1]), reverse=True):
        text = text[:start] + replacement + text[end:]
    updated = text.encode("utf-8")
    after = load_object(updated, path)

    before_other = {key: value for key, value in before.items() if key not in MUTABLE_KEYS}
    after_other = {key: value for key, value in after.items() if key not in MUTABLE_KEYS}
    require(before_other == after_other, f"{path}: a field outside status/quarantine_reason changed")
    require(after.get("status") == "quarantined", f"{path}: status was not quarantined")
    require(after.get("quarantine_reason") == reason, f"{path}: quarantine reason mismatch")
    require(sensitive_scalars(before) == sensitive_scalars(after), f"{path}: path/digest scalar count changed")
    return updated


def prepare(root: Path) -> tuple[dict[Path, bytes], dict[str, Any]]:
    manifest_dir = root / "run-manifests"
    paths = sorted(manifest_dir.glob("*.json"))
    require(len(paths) == EXPECTED_MANIFESTS, f"manifest population is {len(paths)}, expected {EXPECTED_MANIFESTS}")
    tracked = tracked_paths(root)

    affected: list[tuple[Path, dict[str, Any], list[tuple[str, str]]]] = []
    for path in paths:
        manifest = load_object(path.read_bytes(), path)
        missing = [
            (field, value)
            for field, value in declared_evidence(manifest)
            if normalized_repo_path(value) not in tracked
        ]
        if missing:
            affected.append((path, manifest, missing))

    bulk = [row for row in affected if str(row[1].get("run_id", "")).startswith(BULK_PREFIX)]
    remainder = [row for row in affected if str(row[1].get("run_id", "")).startswith(REMAINDER_PREFIX)]
    other = [row for row in affected if row not in bulk and row not in remainder]
    reference_count = sum(len(row[2]) for row in affected)
    bulk_references = sum(len(row[2]) for row in bulk)
    remainder_references = sum(len(row[2]) for row in remainder)

    require(not other, "affected population contains a manifest outside bulk/remainder")
    require(len(affected) == EXPECTED_AFFECTED, f"affected manifests are {len(affected)}, expected {EXPECTED_AFFECTED}")
    require(reference_count == EXPECTED_REFERENCES, f"missing references are {reference_count}, expected {EXPECTED_REFERENCES}")
    require(len(bulk) == EXPECTED_BULK_MANIFESTS, f"bulk manifests are {len(bulk)}, expected {EXPECTED_BULK_MANIFESTS}")
    require(bulk_references == EXPECTED_BULK_REFERENCES, f"bulk references are {bulk_references}, expected {EXPECTED_BULK_REFERENCES}")
    require(len(remainder) == EXPECTED_REMAINDER_MANIFESTS, f"remainder manifests are {len(remainder)}, expected {EXPECTED_REMAINDER_MANIFESTS}")
    require(remainder_references == EXPECTED_REMAINDER_REFERENCES, f"remainder references are {remainder_references}, expected {EXPECTED_REMAINDER_REFERENCES}")

    output_paths = [value for _, manifest, _ in affected for value in nested_paths(manifest.get("outputs"))]
    missing_outputs = [value for value in output_paths if normalized_repo_path(value) not in tracked]
    require(len(output_paths) == EXPECTED_EXISTING_OUTPUT_REFERENCES, f"affected output references are {len(output_paths)}, expected {EXPECTED_EXISTING_OUTPUT_REFERENCES}")
    if missing_outputs:
        raise MigrationError(f"affected output reference is absent: {missing_outputs[0]}")

    before_status = Counter(str(manifest.get("status")) for _, manifest, _ in affected)
    updates: dict[Path, bytes] = {}
    protected_scalars = 0
    for path, manifest, _ in affected:
        raw = path.read_bytes()
        updated = rewrite_manifest(raw, path, manifest)
        protected_scalars += sensitive_scalars(manifest)
        if updated != raw:
            updates[path] = updated

    summary = {
        "head": git_output(root, "rev-parse", "HEAD").strip(),
        "manifests_total": len(paths),
        "affected_manifests": len(affected),
        "missing_references": reference_count,
        "bulk": {"manifests": len(bulk), "references": bulk_references},
        "remainder": {"manifests": len(remainder), "references": remainder_references},
        "existing_output_references_untouched": len(output_paths),
        "protected_path_digest_scalars": protected_scalars,
        "status_before": dict(sorted(before_status.items())),
        "status_after": {"quarantined": len(affected)},
        "files_requiring_change": len(updates),
    }
    return updates, summary


def write_transaction(updates: dict[Path, bytes]) -> None:
    originals = {path: path.read_bytes() for path in updates}
    prepared: dict[Path, Path] = {}
    replaced: list[Path] = []
    try:
        for path, raw in updates.items():
            with tempfile.NamedTemporaryFile(
                mode="wb", prefix=f".{path.name}.", suffix=".tmp", dir=path.parent, delete=False
            ) as handle:
                handle.write(raw)
                handle.flush()
                os.fsync(handle.fileno())
                temporary = Path(handle.name)
            os.chmod(temporary, stat.S_IMODE(path.stat().st_mode))
            prepared[path] = temporary

        for path in updates:
            os.replace(prepared[path], path)
            replaced.append(path)
    except OSError as exc:
        rollback_errors: list[str] = []
        for path in reversed(replaced):
            try:
                with tempfile.NamedTemporaryFile(
                    mode="wb", prefix=f".{path.name}.", suffix=".rollback", dir=path.parent, delete=False
                ) as handle:
                    handle.write(originals[path])
                    handle.flush()
                    os.fsync(handle.fileno())
                    rollback = Path(handle.name)
                os.chmod(rollback, stat.S_IMODE(path.stat().st_mode))
                os.replace(rollback, path)
            except OSError as rollback_exc:
                rollback_errors.append(f"{path}: {rollback_exc}")
        detail = f"write transaction failed and was rolled back: {exc}"
        if rollback_errors:
            detail += "; rollback failures: " + "; ".join(rollback_errors)
        raise MigrationError(detail) from exc
    finally:
        for temporary in prepared.values():
            try:
                temporary.unlink(missing_ok=True)
            except OSError:
                pass


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true", help="write the fully validated migration")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]

    try:
        actual_root = Path(git_output(root, "rev-parse", "--show-toplevel").strip()).resolve()
        require(actual_root == root.resolve(), f"script root {root} differs from Git root {actual_root}")
        updates, summary = prepare(root)
        summary["mode"] = "apply" if args.apply else "check"
        if args.apply:
            write_transaction(updates)
            post_updates, post_summary = prepare(root)
            require(not post_updates, f"idempotence check found {len(post_updates)} remaining changes")
            summary["written_files"] = len(updates)
            summary["post_apply_files_requiring_change"] = post_summary["files_requiring_change"]
        print(json.dumps(summary, indent=2, sort_keys=True))
        return 0
    except MigrationError as exc:
        print(f"REJECTED: {exc}", file=os.sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
