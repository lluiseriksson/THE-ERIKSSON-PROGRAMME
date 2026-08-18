#!/usr/bin/env python3
"""Fail-closed audit for a P0--P9 v18 Colab evidence archive.

The v18 runner retains every child's complete combined stdout/stderr as a
stage log.  This checker verifies those logs against the digests recorded in
``evidence.json`` without extracting untrusted archive paths to disk.
"""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import sys
import tarfile
import tempfile


SOURCE_SHA = "c537ea3babcc1770570f9a131e11e8f11d6806ba"
RUNNER_REV = "p0-p9-prefix-combes-thomas-v19"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
EVIDENCE_ROOT = "hrpoly-p0-p9-prefix-combes-thomas-evidence"


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def read_regular_members(path: Path) -> dict[str, bytes]:
    members: dict[str, bytes] = {}
    with tarfile.open(path, "r:gz") as archive:
        for member in archive.getmembers():
            name = PurePosixPath(member.name)
            if name.is_absolute() or ".." in name.parts:
                raise ValueError(f"unsafe archive path: {member.name}")
            if member.isdir():
                continue
            if not member.isfile():
                raise ValueError(f"non-regular archive member: {member.name}")
            if member.name in members:
                raise ValueError(f"duplicate archive member: {member.name}")
            stream = archive.extractfile(member)
            if stream is None:
                raise ValueError(f"unreadable archive member: {member.name}")
            members[member.name] = stream.read()
    return members


def audit(path: Path) -> str:
    archive_bytes = path.read_bytes()
    members = read_regular_members(path)
    evidence_name = f"{EVIDENCE_ROOT}/evidence.json"
    if evidence_name not in members:
        raise ValueError("evidence.json missing")
    evidence = json.loads(members[evidence_name].decode("utf-8"))
    for key, expected in (
        ("source_sha", SOURCE_SHA),
        ("runner_rev", RUNNER_REV),
        ("mathlib_sha", MATHLIB_SHA),
    ):
        if evidence.get(key) != expected:
            raise ValueError(f"{key}={evidence.get(key)!r}, expected={expected!r}")
    status = evidence.get("status")
    if status not in {"PASS", "FAIL"}:
        raise ValueError(f"invalid status: {status!r}")
    records = evidence.get("records")
    if not isinstance(records, list) or not records:
        raise ValueError("nonempty records list missing")

    stages: set[str] = set()
    failed: list[str] = []
    expected_members = {evidence_name}
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            raise ValueError(f"record {index} is not an object")
        stage = record.get("stage")
        exit_code = record.get("exit")
        output_hash = record.get("output_sha256")
        log_name = record.get("log")
        if not isinstance(stage, str) or not stage:
            raise ValueError(f"record {index} has invalid stage")
        if stage in stages:
            raise ValueError(f"duplicate stage: {stage}")
        stages.add(stage)
        if not isinstance(exit_code, int):
            raise ValueError(f"record {index} has invalid exit")
        if not isinstance(output_hash, str) or len(output_hash) != 64:
            raise ValueError(f"record {index} has invalid output digest")
        if not isinstance(log_name, str) or PurePosixPath(log_name).name != log_name:
            raise ValueError(f"record {index} has unsafe log name")
        member_name = f"{EVIDENCE_ROOT}/{log_name}"
        expected_members.add(member_name)
        if member_name not in members:
            raise ValueError(f"stage log missing: {stage}")
        measured = sha256(members[member_name])
        if measured != output_hash:
            raise ValueError(
                f"stage log hash mismatch: {stage}={measured}, expected={output_hash}"
            )
        if exit_code != 0:
            failed.append(stage)
            if index != len(records) - 1:
                raise ValueError(f"nonterminal failure violates stop-on-first-error: {stage}")

    extras = sorted(set(members) - expected_members)
    if extras:
        raise ValueError(f"unexpected archive members: {extras}")
    if (status == "PASS") != (not failed):
        raise ValueError(f"status/failure mismatch: status={status}, failed={failed}")
    first_fail = failed[0] if failed else "none"
    return (
        "P0_P9_EVIDENCE_ARCHIVE_OK "
        f"status={status} records={len(records)} first_fail={first_fail} "
        f"archive_sha256={sha256(archive_bytes)}"
    )


def fixture_archive(path: Path, *, tamper: bool = False) -> None:
    logs = {"one.log": b"ok\n", "two.log": b"bad\n"}
    evidence = {
        "source_sha": SOURCE_SHA,
        "runner_rev": RUNNER_REV,
        "mathlib_sha": MATHLIB_SHA,
        "status": "FAIL",
        "records": [
            {
                "stage": "one",
                "exit": 0,
                "seconds": 1.0,
                "output_sha256": sha256(logs["one.log"]),
                "log": "one.log",
            },
            {
                "stage": "two",
                "exit": 1,
                "seconds": 2.0,
                "output_sha256": sha256(logs["two.log"]),
                "log": "two.log",
            },
        ],
    }
    if tamper:
        logs["two.log"] = b"tampered\n"
    with tarfile.open(path, "w:gz") as archive:
        payloads = {
            f"{EVIDENCE_ROOT}/evidence.json":
                (json.dumps(evidence, sort_keys=True) + "\n").encode(),
            **{f"{EVIDENCE_ROOT}/{name}": body for name, body in logs.items()},
        }
        for name, body in payloads.items():
            info = tarfile.TarInfo(name)
            info.size = len(body)
            archive.addfile(info, io.BytesIO(body))


def selftest() -> int:
    with tempfile.TemporaryDirectory() as directory:
        good = Path(directory) / "good.tar.gz"
        bad = Path(directory) / "bad.tar.gz"
        fixture_archive(good)
        fixture_archive(bad, tamper=True)
        if not audit(good).startswith("P0_P9_EVIDENCE_ARCHIVE_OK"):
            raise AssertionError("good fixture rejected")
        try:
            audit(bad)
        except ValueError as error:
            if "hash mismatch" not in str(error):
                raise
        else:
            raise AssertionError("tampered fixture accepted")
    print("P0_P9_EVIDENCE_ARCHIVE_SELFTEST_OK")
    return 0


def main() -> int:
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        return selftest()
    if len(sys.argv) != 2:
        raise SystemExit("usage: audit_p0_p9_evidence_archive.py ARCHIVE.tar.gz")
    try:
        print(audit(Path(sys.argv[1])))
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        print(f"P0_P9_EVIDENCE_ARCHIVE_FAIL {error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
