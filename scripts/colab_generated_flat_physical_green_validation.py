#!/usr/bin/env python3
"""Hash-gated Colab validation for the canonical generated flat Green."""

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
            "RUNNER_REV": "generated-flat-physical-green-v2",
            "SOURCE_SHA": "3d5d39a90a968a4bdbb9be49432c6a3378e2147a",
            "ROOT": Path("/content/hrpoly-generated-flat-physical-green"),
            "EVIDENCE": Path(
                "/content/hrpoly-generated-flat-physical-green-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-generated-flat-physical-green-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-generated-flat-physical-green-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreen.lean":
                    "b3ba8b8d1fae7c689d4f4a7ed93eb733e6cb639d67d159f97355ba95c09c80c7",
                "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenAudit.lean":
                    "6bb3b44d59db6b64b29dd235a0900a66be76738dbfb64935eb675bbc2a4d53a6",
            },
            "QUEUE": [
                (
                    "generated_flat_physical_green_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceGeneratedFlatPhysicalGreen",
                    ],
                    None,
                ),
                (
                    "generated_flat_physical_green_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceGeneratedFlatPhysicalGreenAudit.lean",
                    ],
                    5,
                ),
            ],
            "RECORDS": [],
        }
    )
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
