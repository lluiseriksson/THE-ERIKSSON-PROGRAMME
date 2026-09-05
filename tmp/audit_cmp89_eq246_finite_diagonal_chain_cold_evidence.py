#!/usr/bin/env python3
"""Fail-closed verifier for the CMP89 finite-diagonal Colab evidence archive."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import tarfile


EXPECTED_RUNNER = "cmp89-eq246-finite-diagonal-chain-cold-v1"
EXPECTED_SOURCE = "c1cdd849d0117cdf18724ac076cd4a5bbfd67b35"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralCorrectionBound.lean": "996d20df188640c8a807da0cf35133241cc8540805ee5e22db75f2934781d968",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralCorrectionBoundAudit.lean": "a40ed4762d302b41572167946bd5d9b83e3a8a86d9a7e2a9dd62862661707e8e",
    "YangMills/RG/BalabanCMP89Eq251HalfAliasTailIntegral.lean": "4c5b04379529d787d8e50cfe4be800fc40b1351f472bf65f8dfbf50536611b1c",
    "YangMills/RG/BalabanCMP89Eq251HalfAliasTailIntegralAudit.lean": "34fda564a9c88235ae8c739197526845a5d6f7bf9012d3f52a9aaf404cbe56a0",
    "YangMills/RG/BalabanCMP89Eq251BareInverseLaplacianHalfWeight.lean": "2e6ebfaf646e4a41def63bf398786790c4f5958ced4c4b24fd52321f687e8606",
    "YangMills/RG/BalabanCMP89Eq251BareInverseLaplacianHalfWeightAudit.lean": "d01bb463e9f09b1db0680c2a2aa600f608eae809b72ba452d73d83f1b49ea3e7",
    "YangMills/RG/BalabanCMP89Eq251CenteredHalfAliasSum.lean": "bbf0234f73f27d02ec97c5f1220ab7755905cec4491c7a239a98b2e10c6c7f18",
    "YangMills/RG/BalabanCMP89Eq251CenteredHalfAliasSumAudit.lean": "e360002e4f5f90cca46299c4183a52626889474ef0a03ceab39500bac0520553",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceBareDiagonalBound.lean": "b29f637585bf518ae98a5789bce524e4ae294f8fa99eeab5778aea0d8efd11e4",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceBareDiagonalBoundAudit.lean": "7c14d0baef8e1825d4d67a4f8495d9429b87b7fa46ad5f6663a037c72413f3a3",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceBareDiagonalSum.lean": "e9a4ba8557ce3edfca96c0f9960ce8d2de3e4f9fb9b59c1faf9407ffb89fba99",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceBareDiagonalSumAudit.lean": "f8a2d5ed50cae8b225cf2ce1521b9814b9497f94e4ed02e7cf63b7a24b96d23d",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralCorrectionSum.lean": "f526bae53df34b31c891e147d9ab4a9b7a4afceb3a03f190fcb92e9181be738b",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralCorrectionSumAudit.lean": "c357d2941c6e7c7076e46bc6d06ba10c5f03b05f4c76f8b5585a80c8c5c15d11",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralSolutionSum.lean": "67fe60511421973758fcc8ede0c762d91114baba5a1e5da7a29b77458c1a05ef",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralSolutionSumAudit.lean": "86a995125df15f333892224b5645a8f2e9c0fbb7c98dcd57b184597205d78d7b",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceCentralNumeratorIdentity.lean": "84e4f7db8ab83fa5c1459790a684026ec7b4bd4d069fc45d4383ba7d9e8915ca",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceCentralNumeratorIdentityAudit.lean": "32fe866f0a19741bd4f55224465d73ca25a860007e04b6df01fbffc83fdbb8bf",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceCentralComponentBound.lean": "010adeac0b9c63073bff65843b5af4a5cc75345f4ed1cd72012396526be04383",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceCentralComponentBoundAudit.lean": "4291b4df82274e8164f49626f5af5a44b449b40fe3c5baeae17ad9fa15346bd1",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceFullSolutionSum.lean": "0eab7af11e26f03b414baff2f94f195258850f3d5e991d170f668b573b53a2d4",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceFullSolutionSumAudit.lean": "2df9efa762e214ae926640009dbd611644ea88d0f9de5179539ac81c4530e1d1",
}
EXPECTED_QUEUE = ["finite_diagonal_chain_focal"] + [
    f"finite_diagonal_audit_{key}" for key in range(101, 112)
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
        "status": "PASS",
        "source_blobs": EXPECTED_BLOBS,
    }
    for key, expected in required.items():
        if payload.get(key) != expected:
            raise RuntimeError(
                f"EVIDENCE_FIELD_MISMATCH key={key} expected={expected!r} actual={payload.get(key)!r}"
            )
    records = payload.get("records")
    if not isinstance(records, list) or not records:
        raise RuntimeError("RECORDS_MISSING")
    for record in records:
        if record.get("exit") != 0:
            raise RuntimeError(f"NONZERO_RECORD={record!r}")
        if not isinstance(record.get("output_sha256"), str) or len(record["output_sha256"]) != 64:
            raise RuntimeError(f"INVALID_OUTPUT_HASH={record!r}")
    stages = [record.get("stage") for record in records]
    if stages[-len(EXPECTED_QUEUE):] != EXPECTED_QUEUE:
        raise RuntimeError(
            f"QUEUE_STAGE_MISMATCH expected={EXPECTED_QUEUE!r} actual={stages[-len(EXPECTED_QUEUE):]!r}"
        )
    print("CMP89_EQ246_FINITE_DIAGONAL_COLD_EVIDENCE_OK")
    print(f"SOURCE_SHA={EXPECTED_SOURCE}")
    print(f"RECORDS={len(records)}")
    print(f"QUEUE_STAGES={len(EXPECTED_QUEUE)}")
    print(f"SOURCE_BLOBS={len(EXPECTED_BLOBS)}")
    print(f"EVIDENCE_JSON_SHA256={hashlib.sha256(raw).hexdigest().upper()}")
    print(f"ARCHIVE_SHA256={sha256(archive).upper()}")


if __name__ == "__main__":
    main()
