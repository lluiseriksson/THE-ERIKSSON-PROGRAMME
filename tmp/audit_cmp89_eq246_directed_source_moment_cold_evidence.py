#!/usr/bin/env python3
"""Fail-closed verifier for the cold CMP89 directed source-moment gate."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import tarfile


EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
EXPECTED_CONFIGS = {
    "cmp89-eq246-directed-source-moment-cold-v1": {
        "source_sha": "6ae9648a61be6f5be62b351b2c0ab2da1c45cfe9",
        "source_blobs": {
            "YangMills/RG/BalabanCMP89Eq246DirectedSourceMoment.lean":
                "8ad29f284e6e0a321e55a4a607c8741549a52a60073a33e690a43f3365392300",
            "YangMills/RG/BalabanCMP89Eq246DirectedSourceMomentAudit.lean":
                "d6d92c3806739f36efed59ac8c49d86563ea90e8fd64314ab34b13379143e497",
        },
    },
    "cmp89-eq246-directed-source-moment-cold-v2": {
        "source_sha": "e8a1b6be6862256a75cf34f55dae94a48b2e1a37",
        "source_blobs": {
            "YangMills/RG/BalabanCMP89Eq246DirectedSourceMoment.lean":
                "4becef682d69d45714e70848afe7a561b287d42716ffc30972dfca4f0d8ece46",
            "YangMills/RG/BalabanCMP89Eq246DirectedSourceMomentAudit.lean":
                "d6d92c3806739f36efed59ac8c49d86563ea90e8fd64314ab34b13379143e497",
        },
    },
}
EXPECTED_QUEUE = ["directed_source_moment_focal", "directed_source_moment_audit"]


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    archive = parser.parse_args().archive.resolve()
    if not archive.is_file():
        raise RuntimeError(f"ARCHIVE_MISSING={archive}")
    with tarfile.open(archive, "r:gz") as bundle:
        files = [member for member in bundle.getmembers() if member.isfile()]
        if len(files) != 1 or not files[0].name.endswith("/evidence.json"):
            raise RuntimeError(f"ARCHIVE_SCOPE_MISMATCH={[m.name for m in files]}")
        stream = bundle.extractfile(files[0])
        if stream is None:
            raise RuntimeError("EVIDENCE_UNREADABLE")
        raw = stream.read()
    payload = json.loads(raw)
    runner_rev = payload.get("runner_rev")
    config = EXPECTED_CONFIGS.get(runner_rev)
    if config is None:
        raise RuntimeError(f"RUNNER_REV_MISMATCH={runner_rev!r}")
    expected_source = config["source_sha"]
    expected_blobs = config["source_blobs"]
    required = {
        "runner_rev": runner_rev,
        "source_sha": expected_source,
        "mathlib_sha": EXPECTED_MATHLIB,
        "toolchain_asset_sha256": EXPECTED_TOOLCHAIN,
        "minimum_ram_gib": 11.0,
        "gpu_runtime_authorized": False,
    }
    for key, expected in required.items():
        if payload.get(key) != expected:
            raise RuntimeError(
                f"EVIDENCE_FIELD_MISMATCH key={key} expected={expected!r} "
                f"actual={payload.get(key)!r}"
            )
    if payload.get("source_blobs") != expected_blobs:
        raise RuntimeError("SOURCE_BLOB_GATE_MISMATCH")
    status = payload.get("status")
    if status not in {"PASS", "FAIL"}:
        raise RuntimeError(f"INVALID_STATUS={status!r}")
    records = payload.get("records")
    if not isinstance(records, list) or not records:
        raise RuntimeError("RECORDS_MISSING")
    for record in records:
        if not isinstance(record.get("output_sha256"), str) or len(record["output_sha256"]) != 64:
            raise RuntimeError(f"INVALID_OUTPUT_HASH={record!r}")
        if not isinstance(record.get("exit"), int):
            raise RuntimeError(f"INVALID_EXIT={record!r}")
        if not isinstance(record.get("seconds"), (int, float)) or record["seconds"] < 0:
            raise RuntimeError(f"INVALID_DURATION={record!r}")
    record_stages = [record.get("stage") for record in records]
    try:
        queue_start = record_stages.index(EXPECTED_QUEUE[0])
    except ValueError as error:
        raise RuntimeError("QUEUE_START_MISSING") from error
    queue_records = records[queue_start:]
    if len(queue_records) > len(EXPECTED_QUEUE):
        raise RuntimeError(f"QUEUE_HAS_EXTRA_RECORDS={queue_records!r}")
    stages = [record.get("stage") for record in queue_records]
    if stages != EXPECTED_QUEUE[: len(queue_records)]:
        raise RuntimeError(f"QUEUE_STAGE_MISMATCH={stages!r}")
    exits = [record.get("exit") for record in queue_records]
    if status == "PASS" and (stages != EXPECTED_QUEUE or any(code != 0 for code in exits)):
        raise RuntimeError(f"PASS_QUEUE_INCOMPLETE stages={stages!r} exits={exits!r}")
    if status == "FAIL" and (
        not exits or exits[-1] == 0 or any(code != 0 for code in exits[:-1])
    ):
        raise RuntimeError(f"FAIL_STOP_GATE_MISMATCH exits={exits!r}")
    print("CMP89_EQ246_DIRECTED_SOURCE_MOMENT_COLD_EVIDENCE_OK")
    print(f"STATUS={status}")
    print(f"SOURCE_SHA={expected_source}")
    print(f"RECORDS={len(records)}")
    print(f"QUEUE_STAGES={len(queue_records)}")
    print(f"SOURCE_BLOBS={len(expected_blobs)}")
    print(f"EVIDENCE_JSON_SHA256={hashlib.sha256(raw).hexdigest().upper()}")
    print(f"ARCHIVE_SHA256={file_sha256(archive).upper()}")


if __name__ == "__main__":
    main()
