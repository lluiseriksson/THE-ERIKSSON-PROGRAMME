#!/usr/bin/env python3
"""Verify and preserve one C6d next-real-slice FAIL archive.

This is deliberately separate from the PASS verifier: a runner/prerequisite
failure is durable diagnostic evidence but cannot retire PRE-VALIDATION.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--first-error", required=True)
    args = parser.parse_args()

    archive = args.archive.resolve()
    if not archive.is_file():
        raise RuntimeError("C6D_FAILURE_ARCHIVE_MISSING")
    archive_hash = sha256(archive)
    first_error_bytes: bytes | None = None
    with tarfile.open(archive, "r:gz") as tar:
        members = tar.getmembers()
        if not members:
            raise RuntimeError("C6D_FAILURE_ARCHIVE_EMPTY")
        for member in members:
            path = PurePosixPath(member.name)
            if path.is_absolute() or ".." in path.parts:
                raise RuntimeError("C6D_FAILURE_UNSAFE_MEMBER=" + member.name)
        evidence_members = [
            member for member in members if member.name.endswith("/evidence.json")
        ]
        if len(evidence_members) != 1:
            raise RuntimeError("C6D_FAILURE_EVIDENCE_JSON_COUNT")
        extracted = tar.extractfile(evidence_members[0])
        if extracted is None:
            raise RuntimeError("C6D_FAILURE_EVIDENCE_JSON_MISSING")
        evidence = json.loads(extracted.read().decode("utf-8"))
        wanted_log = "/" + args.first_error + ".stdout"
        matching_logs = [
            member for member in members if member.name.endswith(wanted_log)
        ]
        if len(matching_logs) != 1:
            raise RuntimeError("C6D_FAILURE_FIRST_ERROR_LOG_COUNT")
        first_error_stream = tar.extractfile(matching_logs[0])
        if first_error_stream is None:
            raise RuntimeError("C6D_FAILURE_FIRST_ERROR_LOG_MISSING")
        first_error_bytes = first_error_stream.read()

    if evidence.get("status") != "FAIL":
        raise RuntimeError("C6D_FAILURE_STATUS_MISMATCH")
    if evidence.get("source_sha") != args.source_sha:
        raise RuntimeError("C6D_FAILURE_SOURCE_MISMATCH")
    if evidence.get("runner_rev") != args.runner_rev:
        raise RuntimeError("C6D_FAILURE_RUNNER_MISMATCH")
    records = evidence.get("records")
    if not isinstance(records, list) or not records:
        raise RuntimeError("C6D_FAILURE_RECORDS_MISSING")
    failed = [row for row in records if row.get("exit") != 0]
    if len(failed) != 1 or failed[0].get("stage") != args.first_error:
        raise RuntimeError("C6D_FAILURE_FIRST_ERROR_MISMATCH")
    if records[-1] != failed[0]:
        raise RuntimeError("C6D_FAILURE_NOT_STOP_ON_FIRST_ERROR")

    destination = args.destination.resolve()
    if destination.exists():
        raise RuntimeError("C6D_FAILURE_DESTINATION_EXISTS")
    destination.mkdir(parents=True)
    copied = destination / archive.name
    shutil.copy2(archive, copied)
    (destination / "evidence.json").write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    assert first_error_bytes is not None
    (destination / "first-error.stdout").write_bytes(first_error_bytes)
    verification = {
        "archive_sha256": archive_hash,
        "first_error": args.first_error,
        "runner_rev": args.runner_rev,
        "source_sha": args.source_sha,
        "status": "FAIL",
    }
    (destination / "verification.json").write_text(
        json.dumps(verification, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(
        "C6D_NEXT_REAL_SLICE_FAILURE_PRESERVED "
        f"source_sha={args.source_sha} runner_rev={args.runner_rev} "
        f"first_error={args.first_error} archive_sha256={archive_hash} "
        f"destination={destination}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
