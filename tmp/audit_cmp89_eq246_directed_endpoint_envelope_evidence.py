#!/usr/bin/env python3
"""Fail-closed verifier for the directed CMP89 endpoint diagnostic evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import tarfile


EXPECTED_RUNNER = "cmp89-eq246-directed-endpoint-envelope-diagnostic-v1"
EXPECTED_SOURCE = "abc24550519829f7e2c276e2510afbb277f0ec4b"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246DirectedEndpointPhase.lean":
        "83fb277c074bc713901e6fa6d30738d07a1c2823d40513b5939d76db55f81228",
    "YangMills/RG/BalabanCMP89Eq246DirectedEndpointPhaseAudit.lean":
        "446cdb707c10779c92ad6bc662bc0f795b5f4c0c8bae22beb3c623cd49cac4f1",
    "YangMills/RG/BalabanCMP89Eq246SourceEnvelopeMoment.lean":
        "255e51c02c633bdf8f445ce78c81a5305217e5f27b2e0ab03db4d79ab8b62483",
    "YangMills/RG/BalabanCMP89Eq246SourceEnvelopeMomentAudit.lean":
        "6ecd46448982927f7762df6919ce02b3cc73b44b5b259484d769572f42df3278",
}
EXPECTED_QUEUE = [
    "directed_endpoint_phase_focal",
    "directed_endpoint_phase_audit",
    "source_envelope_moment_focal",
    "source_envelope_moment_audit",
]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()
    archive = args.archive.resolve()
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
    required = {
        "runner_rev": EXPECTED_RUNNER,
        "source_sha": EXPECTED_SOURCE,
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
    if payload.get("source_blobs") != EXPECTED_BLOBS:
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
    record_stages = [record.get("stage") for record in records]
    try:
        queue_start = record_stages.index(EXPECTED_QUEUE[0])
    except ValueError as error:
        raise RuntimeError("QUEUE_START_MISSING") from error
    queue_records = records[queue_start:]
    if len(queue_records) > len(EXPECTED_QUEUE):
        raise RuntimeError(f"QUEUE_HAS_EXTRA_RECORDS={queue_records!r}")
    stages = [record.get("stage") for record in queue_records]
    expected_prefix = EXPECTED_QUEUE[: len(queue_records)]
    if stages != expected_prefix:
        raise RuntimeError(
            f"QUEUE_STAGE_MISMATCH expected_prefix={expected_prefix!r} actual={stages!r}"
        )
    exits = [record.get("exit") for record in queue_records]
    if status == "PASS" and (stages != EXPECTED_QUEUE or any(code != 0 for code in exits)):
        raise RuntimeError(f"PASS_QUEUE_INCOMPLETE stages={stages!r} exits={exits!r}")
    if status == "FAIL" and (not exits or exits[-1] == 0 or any(code != 0 for code in exits[:-1])):
        raise RuntimeError(f"FAIL_STOP_GATE_MISMATCH exits={exits!r}")
    print("CMP89_EQ246_DIRECTED_ENDPOINT_ENVELOPE_EVIDENCE_OK")
    print(f"STATUS={status}")
    print(f"SOURCE_SHA={EXPECTED_SOURCE}")
    print(f"RECORDS={len(records)}")
    print(f"QUEUE_STAGES={len(queue_records)}")
    print(f"SOURCE_BLOBS={len(EXPECTED_BLOBS)}")
    print(f"EVIDENCE_JSON_SHA256={hashlib.sha256(raw).hexdigest().upper()}")
    print(f"ARCHIVE_SHA256={sha256(archive).upper()}")


if __name__ == "__main__":
    main()
