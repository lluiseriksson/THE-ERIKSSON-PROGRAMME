#!/usr/bin/env python3
"""Hash-gated Colab validation for the flat generated ambient Laplacian."""

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
            "RUNNER_REV": "flat-generated-ambient-laplacian-v1",
            "SOURCE_SHA": "0d64561a9e8baedf87328619e5bae40973f0918c",
            "ROOT": Path("/content/hrpoly-flat-generated-ambient-laplacian"),
            "EVIDENCE": Path(
                "/content/hrpoly-flat-generated-ambient-laplacian-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-flat-generated-ambient-laplacian-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-flat-generated-ambient-laplacian-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedAmbientLaplacian.lean":
                    "658ca4c253791e816432bbd60d4ae9d84a7c7b5e583f980cb6ed0146c59c52bb",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedAmbientLaplacianAudit.lean":
                    "8de3e915e36d9dd3750f85597c56c38508be519fb16d74651cf077520b94b51b",
            },
            "QUEUE": [
                (
                    "flat_generated_ambient_laplacian_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedAmbientLaplacian",
                    ],
                    None,
                ),
                (
                    "flat_generated_ambient_laplacian_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedAmbientLaplacianAudit.lean",
                    ],
                    1,
                ),
            ],
            "RECORDS": [],
        }
    )
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
