#!/usr/bin/env python3
"""Fail-closed verifier for the CMP89 Neumann kernel/range cold seal."""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_DIR = ROOT / "validation-evidence" / "cmp89-neumann-kernel-range-cold-fd4ca187-20260830"
ARCHIVE = EVIDENCE_DIR / "hrpoly-cmp89-neumann-kernel-range-cold-evidence.tar.gz"
ARCHIVE_SHA256 = "d9aff02bac5576c4b4c93621ac26e0396c9d4d77e39ec2edc20019da41975712"
JSON_SHA256 = "bfe6ddf235f01fd481e549b75a6c3eb7de17743ee33b154f897d20efaaae580e"
SOURCE_SHA = "fd4ca187d4e943c446177ec26d920f6740a87dab"
RUNNER_SHA = "8953e2941c96011abf3237bbe856c1a52f604d2e"
RUNNER_PATH = "scripts/colab_cmp89_neumann_kernel_range_cold_validation.py"
RUNNER_BLOB_SHA256 = "44f98982b28f66c81195aafdce4eca95a64f4c5ae616cbb4db57ff172a7f40a5"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_SHA256 = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"

EXPECTED_STAGES = [
    "download_toolchain", "extract_toolchain", "lean_version", "lake_version",
    "clone", "checkout", "head", "overlay_text_guard", "import_prefix_guard",
    "lake_update", "mathlib_pin", "cache_get",
    "cmp89_neumann_internal_bond_transport_focal",
    "cmp89_neumann_internal_bond_transport_audit",
    "cmp89_neumann_path_transport_focal", "cmp89_neumann_path_transport_audit",
    "cmp89_neumann_one_scale_range_focal", "cmp89_neumann_one_scale_range_audit",
]

EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBondTransport.lean": "3ca601ce233d3c5da92572058677b71a3a4e5d97ce92c50fe3999f1715270913",
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBondTransportAudit.lean": "7b339d2fd3aeb5f965fc5985ed01b504d6a1684e0cb246897d164427e11c5320",
    "YangMills/RG/BalabanCMP89SourceNeumannPathTransport.lean": "9147a2ecd753cf68bde1707fd90e15610b04309f71985bf89481efdc36b14e8d",
    "YangMills/RG/BalabanCMP89SourceNeumannPathTransportAudit.lean": "342404b048690f783be814ee49d823236938d41b6a3f875687c1d70767444670",
    "YangMills/RG/BalabanCMP89SourceNeumannOneScaleRange.lean": "55fe6ac6df9f07156ba87fadc980193298732426cb4c39f33d2e37fba88a14be",
    "YangMills/RG/BalabanCMP89SourceNeumannOneScaleRangeAudit.lean": "5672fb425b1693f45d93c303fad125cfbf491e8d788a0999e5e44af9661bee94",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(rev: str, path: str) -> bytes:
    return subprocess.run(
        ["git", "cat-file", "blob", f"{rev}:{path}"], cwd=ROOT,
        check=True, stdout=subprocess.PIPE,
    ).stdout


def main() -> None:
    archive_bytes = ARCHIVE.read_bytes()
    assert sha256(archive_bytes) == ARCHIVE_SHA256
    with tarfile.open(fileobj=io.BytesIO(archive_bytes), mode="r:gz") as tf:
        names = tf.getnames()
        json_name = "hrpoly-cmp89-neumann-kernel-range-cold-evidence/evidence.json"
        assert names == ["hrpoly-cmp89-neumann-kernel-range-cold-evidence", json_name]
        extracted = tf.extractfile(tf.getmember(json_name))
        assert extracted is not None
        json_bytes = extracted.read()
    assert sha256(json_bytes) == JSON_SHA256
    evidence = json.loads(json_bytes)
    assert evidence["status"] == "PASS"
    assert evidence["runner_rev"] == "cmp89-neumann-kernel-range-cold-v1"
    assert evidence["source_sha"] == SOURCE_SHA
    assert evidence["mathlib_sha"] == MATHLIB_SHA
    assert evidence["toolchain_asset_sha256"] == TOOLCHAIN_SHA256
    assert evidence["source_blobs"] == EXPECTED_BLOBS
    records = evidence["records"]
    assert [record["stage"] for record in records] == EXPECTED_STAGES
    assert all(record["exit"] == 0 and record["seconds"] >= 0 for record in records)
    assert all(re.fullmatch(r"[0-9a-f]{64}", r["output_sha256"]) for r in records)
    for path, expected in EXPECTED_BLOBS.items():
        assert sha256(git_blob(SOURCE_SHA, path)) == expected
    assert sha256(git_blob(RUNNER_SHA, RUNNER_PATH)) == RUNNER_BLOB_SHA256
    print("CMP89_NEUMANN_KERNEL_RANGE_COLD_EVIDENCE_OK")
    print(f"SOURCE_SHA={SOURCE_SHA}")
    print(f"ARCHIVE_SHA256={ARCHIVE_SHA256.upper()}")
    print(f"EVIDENCE_JSON_SHA256={JSON_SHA256.upper()}")
    print(f"STAGES={len(records)} SOURCE_BLOBS={len(EXPECTED_BLOBS)}")


if __name__ == "__main__":
    main()
