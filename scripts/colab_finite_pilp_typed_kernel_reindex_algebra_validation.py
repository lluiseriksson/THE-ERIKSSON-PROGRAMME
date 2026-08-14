#!/usr/bin/env python3
"""Hash-gated Colab validation for exact finite PiLp reindex algebra."""

from __future__ import annotations

import hashlib
import urllib.request
from pathlib import Path


BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/1e7621516004e62634091a45511212f1db4bc484/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)


def main() -> int:
    with urllib.request.urlopen(BASE_RUNNER_URL) as response:
        base_source = response.read()
    actual = hashlib.sha256(base_source).hexdigest()
    print("BASE_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
    if actual != BASE_RUNNER_SHA256:
        raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")

    namespace: dict[str, object] = {"__name__": "colab_validation_base"}
    exec(compile(base_source, BASE_RUNNER_URL, "exec"), namespace)
    namespace.update(
        {
            "RUNNER_REV": "finite-pilp-reindex-algebra-v1",
            "SOURCE_SHA": "442ebf8f0b32ab480a6dc476f51ba8ced9b73f68",
            "ROOT": Path("/content/hrpoly-finite-pilp-reindex-algebra"),
            "EVIDENCE": Path(
                "/content/hrpoly-finite-pilp-reindex-algebra-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-finite-pilp-reindex-algebra-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-finite-pilp-reindex-algebra-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/FinitePiLpTypedKernelReindexAlgebra.lean":
                    "027c1ef07863968dccc3e2454cad39ed0be71d0a0a26a18c2e0ed1673807b8e7",
                "YangMills/RG/FinitePiLpTypedKernelReindexAlgebraAudit.lean":
                    "3a41f55b57054af87f50c4df21fb5f66801a381564e7ba806cf48926d7823313",
            },
            "QUEUE": [
                (
                    "finite_pilp_reindex_algebra_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG.FinitePiLpTypedKernelReindexAlgebra",
                    ],
                    None,
                ),
                (
                    "finite_pilp_reindex_algebra_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "FinitePiLpTypedKernelReindexAlgebraAudit.lean",
                    ],
                    3,
                ),
            ],
            "RECORDS": [],
        }
    )
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
