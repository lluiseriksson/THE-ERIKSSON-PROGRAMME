#!/usr/bin/env python3
"""Fail-closed verifier for the C6d source coercivity/Green cold archive."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile


SOURCE_SHA = "2bb3eb7325b621954a7132d0a8bab3ce2c1bdf24"
RUNNER_REV = "c6d-source-coercivity-green-v1"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_SHA256 = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)
SOURCE_BLOBS_COUNT = 21
SOURCE_BLOBS_SHA256 = (
    "77E278086CC1F952F5C1855D88E1CE7EC4A51725F219F93D900856B51A301D66"
)

MODULES = [
    "BalabanCMP99SourcePoincarePositiveRadiusReachability",
    "BalabanCMP99SourceWeightedGaugePrecisionDictionary",
    "BalabanCMP99Eq360WeightedPrecisionRealSlice",
    "BalabanCMP99SourceActiveRegionTerminalCoercivity",
    "BalabanCMP99Eq360C6dLaplacianRetainedExtension",
    "BalabanCMP99Eq360C6dLocalizedRetainedPrecision",
    "BalabanCMP99Eq360C6dSourceFixedInput",
    "BalabanCMP99Eq360C6dSourceTerminalCoercivity",
    "BalabanCMP99Eq360C6dSourceTerminalCoercivityReachability",
    "BalabanCMP99Eq360C6dSourceBaselineGreen",
]

BOOTSTRAP_STAGES = [
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
]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest().upper()


def safe_members(archive: tarfile.TarFile) -> list[tarfile.TarInfo]:
    members = archive.getmembers()
    for member in members:
        parts = Path(member.name).parts
        if member.name.startswith(("/", "\\")) or ".." in parts:
            raise RuntimeError(f"UNSAFE_ARCHIVE_MEMBER={member.name}")
        if not member.isdir() and not member.isfile():
            raise RuntimeError(f"NONREGULAR_ARCHIVE_MEMBER={member.name}")
    return members


def expected_queue_stages() -> list[str]:
    result = [
        "c6d_source_coercivity_green_materialize_dependencies",
        "c6d_source_coercivity_green_prepare_build_dirs",
    ]
    for index, module in enumerate(MODULES, start=1):
        stem = f"c6d_source_coercivity_green_{index:02d}_{module.lower()}"
        result.extend([stem + "_source", stem + "_audit"])
    result.append("c6d_source_coercivity_green_root")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()

    archive_path = args.archive.resolve()
    if not archive_path.is_file():
        raise RuntimeError(f"ARCHIVE_NOT_FOUND={archive_path}")

    with tarfile.open(archive_path, "r:gz") as archive:
        members = safe_members(archive)
        evidence_members = [
            member for member in members if member.name.endswith("/evidence.json")
        ]
        if len(evidence_members) != 1:
            raise RuntimeError(
                f"EVIDENCE_JSON_COUNT={len(evidence_members)} EXPECTED=1"
            )
        extracted = archive.extractfile(evidence_members[0])
        if extracted is None:
            raise RuntimeError("EVIDENCE_JSON_NOT_A_FILE")
        raw = extracted.read()
        regular_names = [member.name for member in members if member.isfile()]
        if regular_names != [evidence_members[0].name]:
            raise RuntimeError(f"UNEXPECTED_REGULAR_MEMBERS={regular_names!r}")

    payload = json.loads(raw)
    expected_scalars = {
        "runner_rev": RUNNER_REV,
        "source_sha": SOURCE_SHA,
        "mathlib_sha": MATHLIB_SHA,
        "toolchain_asset_sha256": TOOLCHAIN_SHA256,
        "status": "PASS",
    }
    for key, expected in expected_scalars.items():
        actual = payload.get(key)
        if actual != expected:
            raise RuntimeError(f"{key.upper()}={actual!r} EXPECTED={expected!r}")

    source_blobs = payload.get("source_blobs")
    if not isinstance(source_blobs, dict):
        raise RuntimeError("SOURCE_BLOBS_NOT_DICT")
    if len(source_blobs) != SOURCE_BLOBS_COUNT:
        raise RuntimeError(
            f"SOURCE_BLOBS_COUNT={len(source_blobs)} EXPECTED={SOURCE_BLOBS_COUNT}"
        )
    source_blobs_canonical = json.dumps(
        source_blobs, sort_keys=True, separators=(",", ":")
    )
    source_blobs_sha = hashlib.sha256(
        source_blobs_canonical.encode()
    ).hexdigest().upper()
    if source_blobs_sha != SOURCE_BLOBS_SHA256:
        raise RuntimeError(
            f"SOURCE_BLOBS_SHA256={source_blobs_sha} "
            f"EXPECTED={SOURCE_BLOBS_SHA256}"
        )

    records = payload.get("records")
    if not isinstance(records, list):
        raise RuntimeError("RECORDS_NOT_LIST")
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            raise RuntimeError(f"RECORD_{index}_NOT_DICT")
        if set(record) != {"stage", "exit", "seconds", "output_sha256"}:
            raise RuntimeError(f"RECORD_{index}_KEYS={sorted(record)!r}")
        if not isinstance(record["stage"], str):
            raise RuntimeError(f"RECORD_{index}_STAGE_NOT_STRING")
        if type(record["exit"]) is not int:
            raise RuntimeError(f"RECORD_{index}_EXIT_NOT_INT")
        if not isinstance(record["seconds"], (int, float)) or record["seconds"] < 0:
            raise RuntimeError(f"RECORD_{index}_SECONDS={record['seconds']!r}")
        if not isinstance(record["output_sha256"], str) or not re.fullmatch(
            r"[0-9a-f]{64}", record["output_sha256"]
        ):
            raise RuntimeError(
                f"RECORD_{index}_OUTPUT_SHA256={record['output_sha256']!r}"
            )
    stages = [record.get("stage") for record in records]
    exits = [record.get("exit") for record in records]
    if any(exit_code != 0 for exit_code in exits):
        bad = [record for record in records if record.get("exit") != 0]
        raise RuntimeError(f"NONZERO_STAGE={bad!r}")

    queue_stages = expected_queue_stages()
    sanctioned_stage_lists = [
        BOOTSTRAP_STAGES + queue_stages,
        BOOTSTRAP_STAGES[:1]
        + ["apt_update", "install_zstd"]
        + BOOTSTRAP_STAGES[1:]
        + queue_stages,
    ]
    if stages not in sanctioned_stage_lists:
        raise RuntimeError(f"UNSANCTIONED_STAGE_SEQUENCE={stages!r}")

    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    evidence_sha = hashlib.sha256(canonical.encode()).hexdigest().upper()
    archive_sha = sha256(archive_path)
    total_seconds = sum(float(record.get("seconds", 0.0)) for record in records)
    print("C6D_SOURCE_COERCIVITY_GREEN_EVIDENCE_OK")
    print(f"SOURCE_SHA={SOURCE_SHA}")
    print(f"RUNNER_REV={RUNNER_REV}")
    print(f"RECORDS={len(records)}")
    print(f"TOTAL_STAGE_SECONDS={total_seconds:.3f}")
    print(f"EVIDENCE_SHA256={evidence_sha}")
    print(f"ARCHIVE_SHA256={archive_sha}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
