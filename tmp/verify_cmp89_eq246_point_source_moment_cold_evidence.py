#!/usr/bin/env python3
"""Fail-closed verifier for the cold Eq. (2.46) point-source-moment artifact."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tarfile


EXPECTED_SOURCE = "a645d2b833979360f4c62c2b67a34fbec9d3704e"
EXPECTED_RUNNER = "cmp89-eq246-point-source-moment-bound-cold-v1"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_ASSET = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceMomentBound.lean":
        "ec5120365c73b1867668dacad16ce7ef2c94f0930b5a848b4af0e525c1e0bdb8",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceMomentBoundAudit.lean":
        "9131fd1f64e7dd362568dc9803b1a97a50c0c04870945ec7b38ce46067d49fbb",
}
EXPECTED_STAGES = {
    "download_toolchain",
    "apt_update",
    "install_zstd",
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
    "fine_point_source_moment_bound_focal",
    "fine_point_source_moment_bound_audit",
}


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
    records = payload.get("records")
    require(isinstance(records, list), "records is not a list")
    require(all(r.get("exit") == 0 for r in records), "nonzero child exit")
    stages = [r.get("stage") for r in records]
    require(len(stages) == len(set(stages)), "duplicate stage")
    require(set(stages) == EXPECTED_STAGES, f"stage mismatch: {stages}")
    print("CMP89_EQ246_POINT_SOURCE_MOMENT_COLD_EVIDENCE_OK")
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

