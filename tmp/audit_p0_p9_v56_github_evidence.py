#!/usr/bin/env python3
"""Fail-closed audit of the durable GitHub P0--P9 v56 artifact ZIP."""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import tarfile
import zipfile

import github_p0_p9_v56_driver as contract


CONTROL_SHA = "5d802452204ae09d781b4c4172ff5a76a783124b"
DRIVER_SHA256 = "5689D402B227F91382626A3FCDA5D8F2F6023B903DE4AEFD049AF1339162DB78"
DRIVER_PATH = "control/tmp/github_p0_p9_v56_driver.py"
ARCHIVE_NAME = "p0-p9-v56-evidence.tar.gz"
RESULT_MARKER = "P0_P9_V56_GITHUB_EVIDENCE_OK"
BASE_EVIDENCE = {
    "evidence/checkpoint.txt",
    "evidence/control-driver.sha256",
    "evidence/toolchain.txt",
    "evidence/lake-update.log",
    "evidence/mathlib.txt",
    "evidence/cache-get.log",
    "evidence/evidence.json",
    "evidence/axioms.json",
    "evidence/FINAL_STATUS",
    "evidence/SHA256SUMS",
    "evidence/ARCHIVE_SHA256",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_name(raw: str) -> str:
    path = PurePosixPath(raw)
    if path.is_absolute() or ".." in path.parts or raw.endswith("/"):
        raise ValueError(f"unsafe or non-file archive member: {raw}")
    return path.as_posix()


def read_zip(path: Path) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    with zipfile.ZipFile(path) as archive:
        for member in archive.infolist():
            if member.is_dir():
                continue
            name = safe_name(member.filename)
            if name in result:
                raise ValueError(f"duplicate ZIP member: {name}")
            result[name] = archive.read(member)
    return result


def read_tar(payload: bytes) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    with tarfile.open(fileobj=io.BytesIO(payload), mode="r:gz") as archive:
        for member in archive.getmembers():
            if member.isdir():
                continue
            name = safe_name(member.name)
            if not member.isfile() or name in result:
                raise ValueError(f"invalid TAR member: {name}")
            stream = archive.extractfile(member)
            if stream is None:
                raise ValueError(f"unreadable TAR member: {name}")
            result[name] = stream.read()
    return result


def parse_key_values(payload: bytes) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in payload.decode("utf-8").splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        if key in result:
            raise ValueError(f"duplicate key: {key}")
        result[key] = value
    return result


def parse_sums(payload: bytes) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in payload.decode("utf-8").splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if match is None:
            raise ValueError(f"malformed SHA256SUMS row: {line}")
        path = PurePosixPath(match.group(2)).as_posix()
        if path.startswith("./"):
            path = path[2:]
        if path in result:
            raise ValueError(f"duplicate SHA256SUMS path: {path}")
        result[path] = match.group(1)
    return result


def audit(path: Path) -> str:
    outer = read_zip(path)
    if ARCHIVE_NAME not in outer:
        raise ValueError("inner evidence archive missing")
    inner_archive = outer[ARCHIVE_NAME]
    inner = read_tar(inner_archive)

    repo = Path(__file__).resolve().parents[1]
    paths = contract.exact_paths(repo)
    queue = contract.queue(paths)
    expected_logs = {f"evidence/{stage}.log" for stage, _, _ in queue}
    expected_outer = BASE_EVIDENCE | expected_logs | {ARCHIVE_NAME}
    if set(outer) != expected_outer:
        raise ValueError(
            f"outer member scope mismatch missing={sorted(expected_outer - set(outer))} "
            f"extra={sorted(set(outer) - expected_outer)}"
        )
    expected_inner = (expected_outer - {ARCHIVE_NAME, "evidence/ARCHIVE_SHA256"})
    if set(inner) != expected_inner:
        raise ValueError("inner member scope mismatch")
    for name in expected_inner:
        if inner[name] != outer[name]:
            raise ValueError(f"inner/outer byte mismatch: {name}")

    archive_line = outer["evidence/ARCHIVE_SHA256"].decode("utf-8").strip()
    expected_archive_line = f"{sha256(inner_archive)}  {ARCHIVE_NAME}"
    if archive_line != expected_archive_line:
        raise ValueError("inner archive digest mismatch")

    sums = parse_sums(outer["evidence/SHA256SUMS"])
    summed = expected_inner - {"evidence/SHA256SUMS"}
    if set(sums) != summed:
        raise ValueError("SHA256SUMS scope mismatch")
    for name in summed:
        if sums[name] != sha256(outer[name]):
            raise ValueError(f"SHA256SUMS mismatch: {name}")

    checkpoint = parse_key_values(outer["evidence/checkpoint.txt"])
    expected_checkpoint = {
        "SOURCE_SHA": contract.SOURCE_SHA,
        "ACTUAL_SOURCE_HEAD": contract.SOURCE_SHA,
        "CONTROL_SHA": CONTROL_SHA,
        "GITHUB_SHA": CONTROL_SHA,
        "COLD_MODE": "true",
    }
    if checkpoint != expected_checkpoint:
        raise ValueError(f"checkpoint identity mismatch: {checkpoint}")
    driver_line = outer["evidence/control-driver.sha256"].decode("utf-8").strip()
    if driver_line != f"{DRIVER_SHA256.lower()}  {DRIVER_PATH}":
        raise ValueError("control driver digest mismatch")
    if contract.MATHLIB_SHA not in outer["evidence/mathlib.txt"].decode("utf-8"):
        raise ValueError("Mathlib pin readout mismatch")
    toolchain = outer["evidence/toolchain.txt"].decode("utf-8")
    if "Lean (version 4.29.0-rc6" not in toolchain or "Lake version 5.0.0" not in toolchain:
        raise ValueError("Lean/Lake version readout mismatch")

    if outer["evidence/FINAL_STATUS"] != b"FINAL_STATUS=PASS\n":
        raise ValueError("terminal status is not PASS")
    evidence = json.loads(outer["evidence/evidence.json"].decode("utf-8"))
    if evidence.get("source_sha") != contract.SOURCE_SHA:
        raise ValueError("evidence source identity mismatch")
    if evidence.get("mathlib_sha") != contract.MATHLIB_SHA:
        raise ValueError("evidence Mathlib identity mismatch")
    if evidence.get("status") != "PASS" or evidence.get("first_error") is not None:
        raise ValueError("evidence status mismatch")
    records = evidence.get("records")
    if not isinstance(records, list) or len(records) != len(queue):
        raise ValueError("record count mismatch")
    if [record.get("stage") for record in records] != [stage for stage, _, _ in queue]:
        raise ValueError("record order mismatch")

    total_headers = 0
    expected_axioms: dict[str, list[list[str]]] = {}
    for record, (stage, _, expected) in zip(records, queue):
        if record.get("exit") != 0 or record.get("log") != f"{stage}.log":
            raise ValueError(f"malformed record: {stage}")
        log = outer[f"evidence/{stage}.log"]
        if record.get("output_sha256") != sha256(log):
            raise ValueError(f"record log digest mismatch: {stage}")
        text = log.decode("utf-8")
        if expected is not None:
            parsed = contract.parse_axioms(text, expected)
            expected_axioms[stage] = parsed
            total_headers += len(parsed)
    if total_headers != 199 or evidence.get("axiom_headers") != 199:
        raise ValueError("total axiom count mismatch")
    stored_axioms = json.loads(outer["evidence/axioms.json"].decode("utf-8"))
    if stored_axioms != expected_axioms:
        raise ValueError("stored axiom map mismatch")
    if "P0_P9_DIAGNOSTIC_STATIC_OK" not in outer[
        "evidence/p0_p9_static_gate.log"
    ].decode("utf-8"):
        raise ValueError("static gate readout missing")
    if "P0_P9_DIAGNOSTIC_SELFTEST_OK" not in outer[
        "evidence/p0_p9_static_selftest.log"
    ].decode("utf-8"):
        raise ValueError("static self-test readout missing")

    return (
        f"{RESULT_MARKER} "
        f"source_sha={contract.SOURCE_SHA} control_sha={CONTROL_SHA} "
        f"status=PASS stages={len(records)} paths={len(paths)} "
        f"axiom_headers={total_headers} inner_archive_sha256={sha256(inner_archive).upper()} "
        f"outer_zip_sha256={sha256(path.read_bytes()).upper()}"
    )


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("artifact_zip", type=Path)
    args = parser.parse_args()
    print(audit(args.artifact_zip.resolve()))
