#!/usr/bin/env python3
"""Fail-closed verifier for the CMP89 Eq. (2.46) holomorphy archive."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import tarfile


EXPECTED_RUNNER_REV = "cmp89-eq246-fine-point-holomorphy-cold-v3"
EXPECTED_SOURCE = "147e2e2197d57f8f5bc3bb85ebccb0bbaa7f8e06"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)
EXPECTED_SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceHolomorphy.lean":
        "407a55fbec233d3475899830cf484ebe85006f306405cf1d25ced7bb8925840e",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceHolomorphyAudit.lean":
        "3ad677ecbfbb60d7757f2afb742343fdbb0c8c4e03bd46360e83ff58df109b50",
}
REQUIRED_STAGES = {
    "download_toolchain",
    "extract_toolchain",
    "lean_version",
    "lake_version",
    "clone",
    "checkout",
    "head",
    "overlay_text_guard",
    "import_prefix_guard",
    "lake_update",
    "mathlib_pin",
    "cache_get",
    "eq246_fine_point_holomorphy_focal",
    "eq246_fine_point_holomorphy_audit",
}
OPTIONAL_STAGES = {"apt_update", "install_zstd"}


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
    archive_path = args.archive.resolve()
    if not archive_path.is_file():
        raise RuntimeError(f"ARCHIVE_MISSING={archive_path}")

    with tarfile.open(archive_path, mode="r:gz") as archive:
        members = archive.getmembers()
        for member in members:
            if member.name.startswith("/") or ".." in Path(member.name).parts:
                raise RuntimeError(f"UNSAFE_ARCHIVE_MEMBER={member.name}")
        files = [member for member in members if member.isfile()]
        if len(files) != 1 or Path(files[0].name).name != "evidence.json":
            raise RuntimeError(
                "ARCHIVE_SCOPE_MISMATCH=" + repr([member.name for member in members])
            )
        stream = archive.extractfile(files[0])
        if stream is None:
            raise RuntimeError("EVIDENCE_JSON_UNREADABLE")
        raw = stream.read()

    payload = json.loads(raw)
    exact = {
        "runner_rev": EXPECTED_RUNNER_REV,
        "source_sha": EXPECTED_SOURCE,
        "source_blobs": EXPECTED_SOURCE_BLOBS,
        "mathlib_sha": EXPECTED_MATHLIB,
        "toolchain_asset_sha256": EXPECTED_TOOLCHAIN,
        "status": "PASS",
    }
    for key, value in exact.items():
        if payload.get(key) != value:
            raise RuntimeError(
                f"EVIDENCE_FIELD_MISMATCH key={key} "
                f"expected={value!r} actual={payload.get(key)!r}"
            )

    records = payload.get("records")
    if not isinstance(records, list):
        raise RuntimeError("RECORDS_NOT_LIST")
    seen: dict[str, dict[str, object]] = {}
    for record in records:
        if not isinstance(record, dict):
            raise RuntimeError(f"INVALID_RECORD={record!r}")
        stage = record.get("stage")
        if not isinstance(stage, str) or stage in seen:
            raise RuntimeError(f"INVALID_OR_DUPLICATE_STAGE={stage!r}")
        if record.get("exit") != 0:
            raise RuntimeError(f"NONZERO_STAGE={stage}:{record.get('exit')!r}")
        seconds = record.get("seconds")
        if not isinstance(seconds, (int, float)) or seconds < 0:
            raise RuntimeError(f"INVALID_STAGE_SECONDS={stage}:{seconds!r}")
        output_hash = record.get("output_sha256")
        if (
            not isinstance(output_hash, str)
            or len(output_hash) != 64
            or any(char not in "0123456789abcdef" for char in output_hash)
        ):
            raise RuntimeError(f"INVALID_OUTPUT_HASH={stage}:{output_hash!r}")
        seen[stage] = record

    missing = REQUIRED_STAGES - set(seen)
    unexpected = set(seen) - REQUIRED_STAGES - OPTIONAL_STAGES
    if missing or unexpected:
        raise RuntimeError(
            f"STAGE_SCOPE_MISMATCH missing={sorted(missing)} "
            f"unexpected={sorted(unexpected)}"
        )

    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload_hash = hashlib.sha256(canonical.encode()).hexdigest()
    print("CMP89_EQ246_FINE_POINT_HOLOMORPHY_COLAB_EVIDENCE_OK")
    print(f"SOURCE_SHA={EXPECTED_SOURCE}")
    print(f"RUNNER_REV={EXPECTED_RUNNER_REV}")
    print(f"RECORDS={len(records)}")
    for stage in (
        "eq246_fine_point_holomorphy_focal",
        "eq246_fine_point_holomorphy_audit",
    ):
        print(f"STAGE={stage} SECONDS={seen[stage]['seconds']}")
    print(f"EVIDENCE_SHA256={payload_hash.upper()}")
    print(f"ARCHIVE_SHA256={sha256(archive_path).upper()}")


if __name__ == "__main__":
    main()
