"""Quarantine run manifests whose declared script/input evidence is absent.

The migration is intentionally narrow.  Population membership and every
manifest blob are anchored to the exact publication base
``f51d0ee117cb83533382ca6ceb7b02cf6d2f47f2`` and accepted only at the frozen
owner counts.  Only the top-level ``status`` and ``quarantine_reason`` JSON
values may change from that base; every other parsed value, including every
path and digest, is checked before any file is replaced.

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
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import tempfile
from typing import Any, Iterable


BASE_COMMIT = "f51d0ee117cb83533382ca6ceb7b02cf6d2f47f2"
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
OBJECT_ID = re.compile(r"^[0-9a-f]{40,64}$")


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


def git_bytes(root: Path, *args: str, input_bytes: bytes | None = None) -> bytes:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        check=False,
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        if not detail:
            detail = result.stdout.decode("utf-8", errors="replace").strip()
        raise MigrationError(f"git {' '.join(args)} failed: {detail}")
    return result.stdout


def safe_repo_path(raw: bytes) -> str:
    try:
        path = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise MigrationError(f"base tree path is not UTF-8: {exc}") from exc
    pure = PurePosixPath(path)
    require(path == pure.as_posix(), f"invalid base tree path: {path!r}")
    require(not pure.is_absolute(), f"absolute base tree path: {path!r}")
    require("\\" not in path, f"backslash in base tree path: {path!r}")
    require(all(part not in {"", ".", ".."} for part in pure.parts), f"unsafe base tree path: {path!r}")
    require(not any(ord(character) < 32 for character in path), f"control byte in base tree path: {path!r}")
    return path


def base_tree(root: Path) -> dict[str, tuple[str, str, str]]:
    resolved = git_output(root, "rev-parse", "--verify", f"{BASE_COMMIT}^{{commit}}").strip()
    require(resolved == BASE_COMMIT, f"base commit resolved to {resolved!r}, expected {BASE_COMMIT}")
    raw = git_bytes(root, "ls-tree", "-r", "-z", "--full-tree", BASE_COMMIT)
    entries: dict[str, tuple[str, str, str]] = {}
    for record in raw.split(b"\0"):
        if not record:
            continue
        try:
            header, raw_path = record.split(b"\t", 1)
            raw_mode, raw_type, raw_oid = header.split(b" ", 2)
            mode = raw_mode.decode("ascii")
            object_type = raw_type.decode("ascii")
            oid = raw_oid.decode("ascii")
        except (ValueError, UnicodeDecodeError) as exc:
            raise MigrationError(f"invalid base tree record: {record!r}") from exc
        path = safe_repo_path(raw_path)
        require(path not in entries, f"duplicate base tree path: {path}")
        require(OBJECT_ID.fullmatch(oid) is not None, f"invalid blob id for {path}: {oid!r}")
        entries[path] = (mode, object_type, oid)
    require(entries, "base tree is empty")
    return entries


def batch_blobs(root: Path, path_entries: dict[str, tuple[str, str, str]]) -> dict[str, bytes]:
    ordered_oids = list(dict.fromkeys(entry[2] for entry in path_entries.values()))
    request = b"".join(oid.encode("ascii") + b"\n" for oid in ordered_oids)
    response = git_bytes(root, "cat-file", "--batch", input_bytes=request)
    position = 0
    blobs: dict[str, bytes] = {}
    for expected_oid in ordered_oids:
        newline = response.find(b"\n", position)
        require(newline >= 0, f"truncated cat-file header for blob {expected_oid}")
        header = response[position:newline]
        position = newline + 1
        parts = header.split(b" ")
        require(len(parts) == 3, f"invalid cat-file header for blob {expected_oid}: {header!r}")
        try:
            actual_oid = parts[0].decode("ascii")
            object_type = parts[1].decode("ascii")
            size = int(parts[2].decode("ascii"))
        except (UnicodeDecodeError, ValueError) as exc:
            raise MigrationError(f"invalid cat-file header for blob {expected_oid}: {header!r}") from exc
        require(actual_oid == expected_oid, f"cat-file returned {actual_oid!r}, expected {expected_oid}")
        require(object_type == "blob", f"base object {expected_oid} is {object_type}, expected blob")
        require(size >= 0 and position + size < len(response), f"invalid blob size for {expected_oid}: {size}")
        blobs[expected_oid] = response[position : position + size]
        position += size
        require(response[position : position + 1] == b"\n", f"missing cat-file terminator for {expected_oid}")
        position += 1
    require(position == len(response), "unexpected trailing cat-file output")
    return blobs


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


def without_mutable(manifest: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in manifest.items() if key not in MUTABLE_KEYS}


def immutable_lf_members(raw: bytes, path: Path) -> list[tuple[str, str]]:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise MigrationError(f"{path}: not UTF-8: {exc}") from exc
    members, _ = top_level_members(text, path)
    return [
        (key, text[start:end].replace("\r\n", "\n"))
        for key, (start, end) in members.items()
        if key not in MUTABLE_KEYS
    ]


def rewrite_manifest(
    raw: bytes,
    path: Path,
    before: dict[str, Any],
    base: dict[str, Any],
    base_raw: bytes,
    reason: str,
) -> bytes:
    text = raw.decode("utf-8")
    members, last_value_end = top_level_members(text, path)
    require("status" in members, f"{path}: missing top-level status")

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

    require(without_mutable(before) == without_mutable(base), f"{path}: current content differs from base outside status/quarantine_reason")
    require(without_mutable(after) == without_mutable(base), f"{path}: rewrite changed a field outside status/quarantine_reason")
    require(immutable_lf_members(raw, path) == immutable_lf_members(base_raw, path), f"{path}: non-lifecycle LF-normalized JSON bytes differ from base")
    require(immutable_lf_members(updated, path) == immutable_lf_members(base_raw, path), f"{path}: rewrite changed non-lifecycle LF-normalized JSON bytes")
    require(after.get("status") == "quarantined", f"{path}: status was not quarantined")
    require(after.get("quarantine_reason") == reason, f"{path}: quarantine reason mismatch")
    require(sensitive_scalars(base) == sensitive_scalars(after), f"{path}: path/digest scalar count changed")
    return updated


def prepare(root: Path) -> tuple[dict[Path, bytes], dict[str, Any]]:
    manifest_dir = root / "run-manifests"
    tree = base_tree(root)
    manifest_entries = {
        path: entry
        for path, entry in tree.items()
        if path.startswith("run-manifests/")
        and len(PurePosixPath(path).parts) == 2
        and path.endswith(".json")
    }
    require(
        len(manifest_entries) == EXPECTED_MANIFESTS,
        f"base manifest population is {len(manifest_entries)}, expected {EXPECTED_MANIFESTS}",
    )
    for repo_path, (mode, object_type, _) in manifest_entries.items():
        require(object_type == "blob", f"base manifest {repo_path} is {object_type}, expected blob")
        require(mode in {"100644", "100755"}, f"base manifest {repo_path} has invalid mode {mode}")

    worktree_repo_paths = {
        path.relative_to(root).as_posix() for path in manifest_dir.glob("*.json")
    }
    expected_repo_paths = set(manifest_entries)
    missing_paths = sorted(expected_repo_paths - worktree_repo_paths)
    extra_paths = sorted(worktree_repo_paths - expected_repo_paths)
    require(not missing_paths, f"worktree is missing base manifest: {missing_paths[:1]}")
    require(not extra_paths, f"worktree has manifest absent from base: {extra_paths[:1]}")

    blobs = batch_blobs(root, manifest_entries)
    rows: list[
        tuple[Path, bytes, dict[str, Any], dict[str, Any], list[tuple[str, str]]]
    ] = []
    tracked = set(tree)
    for repo_path in sorted(manifest_entries):
        path = root / Path(*PurePosixPath(repo_path).parts)
        require(path.is_file() and not path.is_symlink(), f"invalid worktree manifest path: {repo_path}")
        base_oid = manifest_entries[repo_path][2]
        base_raw = blobs[base_oid]
        current_raw = path.read_bytes()
        base_path = Path(f"{BASE_COMMIT}:{repo_path}")
        base_manifest = load_object(base_raw, base_path)
        current_manifest = load_object(current_raw, path)
        require(
            without_mutable(current_manifest) == without_mutable(base_manifest),
            f"{repo_path}: current content differs from base blob {base_oid} outside status/quarantine_reason",
        )
        require(
            immutable_lf_members(current_raw, path) == immutable_lf_members(base_raw, base_path),
            f"{repo_path}: non-lifecycle LF-normalized JSON bytes differ from base blob {base_oid}",
        )
        missing = [
            (field, value)
            for field, value in declared_evidence(base_manifest)
            if normalized_repo_path(value) not in tracked
        ]
        rows.append((path, base_raw, base_manifest, current_manifest, missing))

    affected = [row for row in rows if row[4]]

    bulk = [row for row in affected if str(row[2].get("run_id", "")).startswith(BULK_PREFIX)]
    remainder = [row for row in affected if str(row[2].get("run_id", "")).startswith(REMAINDER_PREFIX)]
    other = [row for row in affected if row not in bulk and row not in remainder]
    reference_count = sum(len(row[4]) for row in affected)
    bulk_references = sum(len(row[4]) for row in bulk)
    remainder_references = sum(len(row[4]) for row in remainder)

    require(not other, "affected population contains a manifest outside bulk/remainder")
    require(len(affected) == EXPECTED_AFFECTED, f"affected manifests are {len(affected)}, expected {EXPECTED_AFFECTED}")
    require(reference_count == EXPECTED_REFERENCES, f"missing references are {reference_count}, expected {EXPECTED_REFERENCES}")
    require(len(bulk) == EXPECTED_BULK_MANIFESTS, f"bulk manifests are {len(bulk)}, expected {EXPECTED_BULK_MANIFESTS}")
    require(bulk_references == EXPECTED_BULK_REFERENCES, f"bulk references are {bulk_references}, expected {EXPECTED_BULK_REFERENCES}")
    require(len(remainder) == EXPECTED_REMAINDER_MANIFESTS, f"remainder manifests are {len(remainder)}, expected {EXPECTED_REMAINDER_MANIFESTS}")
    require(remainder_references == EXPECTED_REMAINDER_REFERENCES, f"remainder references are {remainder_references}, expected {EXPECTED_REMAINDER_REFERENCES}")

    output_paths = [value for _, _, manifest, _, _ in affected for value in nested_paths(manifest.get("outputs"))]
    missing_outputs = [value for value in output_paths if normalized_repo_path(value) not in tracked]
    require(len(output_paths) == EXPECTED_EXISTING_OUTPUT_REFERENCES, f"affected output references are {len(output_paths)}, expected {EXPECTED_EXISTING_OUTPUT_REFERENCES}")
    if missing_outputs:
        raise MigrationError(f"affected output reference is absent: {missing_outputs[0]}")

    before_status = Counter(str(manifest.get("status")) for _, _, manifest, _, _ in affected)
    updates: dict[Path, bytes] = {}
    protected_scalars = 0
    affected_paths = {path for path, _, _, _, _ in affected}
    for path, base_raw, base_manifest, current_manifest, _ in rows:
        if path not in affected_paths:
            require(current_manifest == base_manifest, f"{path}: unaffected manifest differs from base")
            continue

        reason = replacement_reason(base_manifest)
        base_lifecycle = (
            base_manifest.get("status"),
            base_manifest.get("quarantine_reason"),
        )
        current_lifecycle = (
            current_manifest.get("status"),
            current_manifest.get("quarantine_reason"),
        )
        target_lifecycle = ("quarantined", reason)
        require(
            current_lifecycle == base_lifecycle or current_lifecycle == target_lifecycle,
            f"{path}: status/quarantine_reason is neither the base nor idempotent target state",
        )
        raw = path.read_bytes()
        updated = rewrite_manifest(raw, path, current_manifest, base_manifest, base_raw, reason)
        protected_scalars += sensitive_scalars(base_manifest)
        if updated != raw:
            updates[path] = updated

    summary = {
        "base_commit": BASE_COMMIT,
        "base_manifest_blobs_verified": len(manifest_entries),
        "head": git_output(root, "rev-parse", "HEAD").strip(),
        "manifests_total": len(manifest_entries),
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
