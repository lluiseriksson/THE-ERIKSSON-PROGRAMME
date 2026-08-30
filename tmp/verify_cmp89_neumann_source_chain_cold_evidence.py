#!/usr/bin/env python3
"""Fail-closed verifier for the CMP89 Neumann source-chain cold seal."""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_DIR = (
    ROOT
    / "validation-evidence"
    / "cmp89-neumann-source-chain-cold-a1fe7d15-20260830"
)
ARCHIVE = EVIDENCE_DIR / "hrpoly-cmp89-neumann-source-chain-cold-evidence.tar.gz"
ARCHIVE_SHA256 = "68645d70be9046d230b6fca7503d4011b807e9a7eb7b203ae385e7166099c69f"
JSON_SHA256 = "6b7fa19d2d4d2c0adf9d9a563c9f888cb803fdffb2854fa202c69556092d0a2a"
SOURCE_SHA = "a1fe7d151400d99fe0d89e5d430ddb992a6168b8"
RUNNER_SHA = "e1f0e13c31eee784e4c5e46eafa32da6621e0912"
RUNNER_PATH = "scripts/colab_cmp89_neumann_source_chain_cold_validation.py"
RUNNER_BLOB_SHA256 = "679d7f0a8438c40bcf5bdb4b6989927ab7835dfda416ded9cd6b90c7aae0193f"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_SHA256 = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"

EXPECTED_STAGES = [
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
    "cmp89_neumann_gauge_precision_focal",
    "cmp89_neumann_gauge_precision_audit",
    "cmp89_neumann_poincare_existence_focal",
    "cmp89_neumann_poincare_existence_audit",
    "cmp89_neumann_weighted_counting_focal",
    "cmp89_neumann_weighted_counting_audit",
    "cmp89_canonical_neumann_reflection_focal",
    "cmp89_canonical_neumann_reflection_audit",
]

EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalGaugePrecision.lean":
        "dfef4cef851c6062632098b3ab49971c0bf9cb6fe6ec9f2219f961cff4706a73",
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalGaugePrecisionAudit.lean":
        "3dff5e6ea6a93f743820b9710ac10e295e55587194e7bb826a7580e9c9051e1f",
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalPoincareExistence.lean":
        "b79a070f779583058f0b2cfa984f5b05efc05af34f36f7d3fd4a7a1d577151de",
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalPoincareExistenceAudit.lean":
        "3a3673a2be7178b4a4551fbb2a680f9b045ff2c2039328fba7a8139d77dcef16",
    "YangMills/RG/BalabanCMP89SourceNeumannWeightedCountingDictionary.lean":
        "12e40bfca4885f5defd2536ef64555705e04175d9d88a6eb40d26cb6ab537be2",
    "YangMills/RG/BalabanCMP89SourceNeumannWeightedCountingDictionaryAudit.lean":
        "2bf9522efbace7e746da0d13c66ecbd060b803ada81fe39040fa4768431aa6e4",
    "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionRepresentation.lean":
        "d606f4180d293cb9e1976190333b2736b729006c4c90ed65c678c4e388c6c277",
    "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionRepresentationAudit.lean":
        "bb4f46522fbdc47c705b1b4b00fa53e5d6f6be170c4872210f9d509a9e745df7",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(rev: str, path: str) -> bytes:
    return subprocess.run(
        ["git", "cat-file", "blob", f"{rev}:{path}"],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout


def main() -> None:
    archive_bytes = ARCHIVE.read_bytes()
    assert sha256(archive_bytes) == ARCHIVE_SHA256
    with tarfile.open(fileobj=io.BytesIO(archive_bytes), mode="r:gz") as tf:
        names = tf.getnames()
        expected_json_name = (
            "hrpoly-cmp89-neumann-source-chain-cold-evidence/evidence.json"
        )
        assert names == [
            "hrpoly-cmp89-neumann-source-chain-cold-evidence",
            expected_json_name,
        ]
        member = tf.getmember(expected_json_name)
        extracted = tf.extractfile(member)
        assert extracted is not None
        json_bytes = extracted.read()
    assert sha256(json_bytes) == JSON_SHA256
    evidence = json.loads(json_bytes)
    assert evidence["status"] == "PASS"
    assert evidence["runner_rev"] == "cmp89-neumann-source-chain-cold-v1"
    assert evidence["source_sha"] == SOURCE_SHA
    assert evidence["mathlib_sha"] == MATHLIB_SHA
    assert evidence["toolchain_asset_sha256"] == TOOLCHAIN_SHA256
    assert evidence["source_blobs"] == EXPECTED_BLOBS
    records = evidence["records"]
    assert [record["stage"] for record in records] == EXPECTED_STAGES
    assert all(record["exit"] == 0 for record in records)
    assert all(record["seconds"] >= 0 for record in records)
    assert all(
        re.fullmatch(r"[0-9a-f]{64}", record["output_sha256"])
        for record in records
    )
    for path, expected in EXPECTED_BLOBS.items():
        assert sha256(git_blob(SOURCE_SHA, path)) == expected
    assert sha256(git_blob(RUNNER_SHA, RUNNER_PATH)) == RUNNER_BLOB_SHA256
    print("CMP89_NEUMANN_SOURCE_CHAIN_COLD_EVIDENCE_OK")
    print(f"SOURCE_SHA={SOURCE_SHA}")
    print(f"ARCHIVE_SHA256={ARCHIVE_SHA256.upper()}")
    print(f"EVIDENCE_JSON_SHA256={JSON_SHA256.upper()}")
    print(f"STAGES={len(records)} SOURCE_BLOBS={len(EXPECTED_BLOBS)}")


if __name__ == "__main__":
    main()
