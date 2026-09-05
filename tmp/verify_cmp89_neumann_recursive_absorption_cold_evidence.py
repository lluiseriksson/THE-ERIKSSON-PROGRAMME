#!/usr/bin/env python3
"""Fail-closed verifier for the CMP89 Neumann recursion/absorption cold seal."""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_DIR = ROOT / "validation-evidence" / "cmp89-neumann-recursive-absorption-cold-93c98c4f-20260830"
ARCHIVE = EVIDENCE_DIR / "hrpoly-cmp89-neumann-recursive-absorption-cold-evidence.tar.gz"
ARCHIVE_SHA256 = "6cb9f6f319c8807b47f1ebdf32ed285e58a91c14b70675c8db2511fb0226c367"
JSON_SHA256 = "87bb7e1ac12c092c7af2c6dc5df2ad9d34c9901ced84bc6e9ef28fdd8c49778d"
SOURCE_SHA = "93c98c4facfa98ec772ee81b8f9498a7ada59e4c"
RUNNER_SHA = "616f6ca334dceed629bb78cdbc1efbe80af65854"
RUNNER_PATH = "scripts/colab_cmp89_neumann_recursive_absorption_cold_validation.py"
RUNNER_BLOB_SHA256 = "e7cffed9b11fe0333ecc76e7757472fe23f0f3776263a5d231a67ee35cf1ee27"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_SHA256 = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"

EXPECTED_STAGES = [
    "download_toolchain", "extract_toolchain", "lean_version", "lake_version",
    "clone", "checkout", "head", "overlay_text_guard", "import_prefix_guard",
    "lake_update", "mathlib_pin", "cache_get",
    "cmp89_neumann_one_scale_poincare_focal",
    "cmp89_neumann_one_scale_poincare_audit",
    "cmp89_neumann_parallel_defect_focal",
    "cmp89_neumann_parallel_defect_audit",
    "cmp89_neumann_recursive_defect_focal",
    "cmp89_neumann_recursive_defect_audit",
    "cmp89_neumann_kernel_absorption_focal",
    "cmp89_neumann_kernel_absorption_audit",
]

EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannKernelAbsorption.lean": "b3b6500ab17d62399c20df0de91b31fdea368ef609ea8297ce1468d68a62d64d",
    "YangMills/RG/BalabanCMP89SourceNeumannKernelAbsorptionAudit.lean": "8b1856a6a16ef313fbdff5459fa666860074d1a1b99a82b9ae45dc2ec5d5ba51",
    "YangMills/RG/BalabanCMP89SourceNeumannOneScalePoincare.lean": "ddb5b7fe7f0206ce4518ae1710b5451817b8d54dc9269a2c163cd1c7022ae0a9",
    "YangMills/RG/BalabanCMP89SourceNeumannOneScalePoincareAudit.lean": "b6734a94fd9c11d59215f6a026da087723c70cd65b8cc5e9f7016459f77332da",
    "YangMills/RG/BalabanCMP89SourceNeumannParallelDefect.lean": "578edab68673d95a288a6573cb8b4384c31f096149ac86e33fb6c13c5a033815",
    "YangMills/RG/BalabanCMP89SourceNeumannParallelDefectAudit.lean": "12895bbf9e064c553808dc6331f52ead552b1b6ba97216317f9d7a7cc643cd43",
    "YangMills/RG/BalabanCMP89SourceNeumannRecursiveDefectBound.lean": "e4db267fccfd8bcfdfc451eaebb004c9589d227b495d2b8eae891b7c1e6670b7",
    "YangMills/RG/BalabanCMP89SourceNeumannRecursiveDefectBoundAudit.lean": "adf038d13550bc6098d27b5521960ed4cd218cd6f878d50d43561560368e778e",
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
        json_name = "hrpoly-cmp89-neumann-recursive-absorption-cold-evidence/evidence.json"
        assert names == ["hrpoly-cmp89-neumann-recursive-absorption-cold-evidence", json_name]
        extracted = tf.extractfile(tf.getmember(json_name))
        assert extracted is not None
        json_bytes = extracted.read()
    assert sha256(json_bytes) == JSON_SHA256
    evidence = json.loads(json_bytes)
    assert evidence["status"] == "PASS"
    assert evidence["runner_rev"] == "cmp89-neumann-recursive-absorption-cold-v1"
    assert evidence["source_sha"] == SOURCE_SHA
    assert evidence["mathlib_sha"] == MATHLIB_SHA
    assert evidence["toolchain_asset_sha256"] == TOOLCHAIN_SHA256
    assert evidence["source_blobs"] == EXPECTED_BLOBS
    records = evidence["records"]
    assert [record["stage"] for record in records] == EXPECTED_STAGES
    assert all(record["exit"] == 0 and record["seconds"] >= 0 for record in records)
    assert all(re.fullmatch(r"[0-9a-f]{64}", record["output_sha256"]) for record in records)
    for path, expected in EXPECTED_BLOBS.items():
        assert sha256(git_blob(SOURCE_SHA, path)) == expected
    assert sha256(git_blob(RUNNER_SHA, RUNNER_PATH)) == RUNNER_BLOB_SHA256
    print("CMP89_NEUMANN_RECURSIVE_ABSORPTION_COLD_EVIDENCE_OK")
    print(f"SOURCE_SHA={SOURCE_SHA}")
    print(f"ARCHIVE_SHA256={ARCHIVE_SHA256.upper()}")
    print(f"EVIDENCE_JSON_SHA256={JSON_SHA256.upper()}")
    print(f"STAGES={len(records)} SOURCE_BLOBS={len(EXPECTED_BLOBS)}")


if __name__ == "__main__":
    main()
