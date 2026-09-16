#!/usr/bin/env python3
"""Fail-closed verifier for the cold Eq. (2.46) central-row reciprocal artifact."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tarfile


EXPECTED_SOURCE = "4584f4c9d2cebe4f61a1ec48681256260deb7090"
EXPECTED_RUNNER = "cmp89-eq246-central-row-reciprocal-cold-v1"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_ASSET = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246CentralAverageRowReciprocalBound.lean":
        "7b2fd3fa817da416cd7507459997d3aa3d95afc3b62b8632f8211e06a6286f3d",
    "YangMills/RG/BalabanCMP89Eq246CentralAverageRowReciprocalBoundAudit.lean":
        "cf431cf3f192f6cc24155e88a4893cef558bca4bfa552df2b81da612068e380e",
}
REQUIRED_STAGES = [
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
    "central_row_reciprocal_focal",
    "central_row_reciprocal_audit",
]
ZSTD_STAGES = ["apt_update", "install_zstd"]
REQUIRED_STAGES_WITH_ZSTD = [
    REQUIRED_STAGES[0],
    *ZSTD_STAGES,
    *REQUIRED_STAGES[1:],
]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> int:
    require(len(sys.argv) == 2, "usage: verifier evidence.tar.gz")
    archive = Path(sys.argv[1]).resolve()
    require(archive.is_file(), f"missing archive: {archive}")
    raw_archive = archive.read_bytes()
    with tarfile.open(archive, "r:gz") as tf:
        members = [m for m in tf.getmembers() if m.isfile()]
        require(len(members) == 1, f"unexpected file members: {[m.name for m in members]}")
        require(members[0].name.endswith("/evidence.json"), members[0].name)
        extracted = tf.extractfile(members[0])
        require(extracted is not None, "cannot extract evidence.json")
        raw_json = extracted.read()
    payload = json.loads(raw_json)
    require(payload.get("status") == "PASS", "status is not PASS")
    require(payload.get("runner_rev") == EXPECTED_RUNNER, "runner mismatch")
    require(payload.get("source_sha") == EXPECTED_SOURCE, "source mismatch")
    require(payload.get("mathlib_sha") == EXPECTED_MATHLIB, "Mathlib mismatch")
    require(payload.get("toolchain_asset_sha256") == EXPECTED_ASSET, "asset mismatch")
    require(payload.get("source_blobs") == EXPECTED_BLOBS, "source-blob mismatch")
    require(payload.get("minimum_ram_gib") == 11.0, "RAM gate mismatch")
    require(payload.get("gpu_runtime_authorized") is False, "GPU authorization mismatch")
    records = payload.get("records")
    require(isinstance(records, list), "records is not a list")
    require(all(r.get("exit") == 0 for r in records), "nonzero child exit")
    stages = [r.get("stage") for r in records]
    require(
        stages in (REQUIRED_STAGES, REQUIRED_STAGES_WITH_ZSTD),
        f"stage mismatch: {stages}",
    )
    print("CMP89_EQ246_CENTRAL_ROW_RECIPROCAL_COLD_EVIDENCE_OK")
    print(f"archive={archive}")
    print(f"archive_sha256={sha256(raw_archive).upper()}")
    print(f"evidence_json_sha256={sha256(raw_json).upper()}")
    for record in records:
        if record["stage"].endswith(("_focal", "_audit")):
            print(
                f"stage={record['stage']} exit={record['exit']} "
                f"seconds={record['seconds']:.3f} output_sha256={record['output_sha256']}"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
