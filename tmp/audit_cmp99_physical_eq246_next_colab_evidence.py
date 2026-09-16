#!/usr/bin/env python3
"""Fail-closed verifier for the cold physical Eq. (2.46) archive."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import tarfile


EXPECTED_RUNNER_REV = "cmp99-physical-eq246-next-cold-v1"
EXPECTED_SOURCE = "76d8aa0c083dd1061ea50580889d0316bc0cad3d"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
EXPECTED_SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution.lean":
        "b95adb2c3026e39b8846b16d8f7aaed07776b7ac63dcb0b9cf72ed6a2651bd78",
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolutionAudit.lean":
        "2afa20a4a147c36e7c474bad0df1f33c814b5a7814ed33f4eb50ca1ed6a7d4bd",
    "YangMills/RG/BalabanCMP99FlatPhysicalFibrePointSourceDFT.lean":
        "393692ae5dd94df1bc2138b24ae1fb198712af0dc7b1a5471b733a3c8bce1a84",
    "YangMills/RG/BalabanCMP99FlatPhysicalFibrePointSourceDFTAudit.lean":
        "9a04dd238d71fb1a73043ccea31930d0aac7eb177a016724c3f43f0516e81221",
}
REQUIRED_STAGES = {
    "download_toolchain", "extract_toolchain", "lean_version", "lake_version",
    "clone", "checkout", "head", "overlay_text_guard", "import_prefix_guard",
    "lake_update", "mathlib_pin", "cache_get",
    "physical_eq246_transpose_full_solution_focal",
    "physical_eq246_transpose_full_solution_audit",
    "physical_point_source_dft_focal", "physical_point_source_dft_audit",
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
            raise RuntimeError("ARCHIVE_SCOPE_MISMATCH=" + repr([m.name for m in members]))
        stream = archive.extractfile(files[0])
        if stream is None:
            raise RuntimeError("EVIDENCE_JSON_UNREADABLE")
        payload = json.loads(stream.read())

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
            raise RuntimeError(f"EVIDENCE_FIELD_MISMATCH key={key} expected={value!r} actual={payload.get(key)!r}")

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
        if not isinstance(output_hash, str) or len(output_hash) != 64 or any(c not in "0123456789abcdef" for c in output_hash):
            raise RuntimeError(f"INVALID_OUTPUT_HASH={stage}:{output_hash!r}")
        seen[stage] = record

    missing = REQUIRED_STAGES - set(seen)
    unexpected = set(seen) - REQUIRED_STAGES - OPTIONAL_STAGES
    if missing or unexpected:
        raise RuntimeError(f"STAGE_SCOPE_MISMATCH missing={sorted(missing)} unexpected={sorted(unexpected)}")

    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    print("CMP99_PHYSICAL_EQ246_NEXT_COLAB_EVIDENCE_OK")
    print(f"SOURCE_SHA={EXPECTED_SOURCE}")
    print(f"RUNNER_REV={EXPECTED_RUNNER_REV}")
    print(f"RECORDS={len(records)}")
    for stage in (
        "physical_eq246_transpose_full_solution_focal",
        "physical_eq246_transpose_full_solution_audit",
        "physical_point_source_dft_focal",
        "physical_point_source_dft_audit",
    ):
        print(f"STAGE={stage} SECONDS={seen[stage]['seconds']}")
    print("EVIDENCE_SHA256=" + hashlib.sha256(canonical.encode()).hexdigest().upper())
    print("ARCHIVE_SHA256=" + sha256(archive_path).upper())


if __name__ == "__main__":
    main()
