#!/usr/bin/env python3
"""Hash-gated Colab validation for complexified flat ambient Green."""

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
            "RUNNER_REV": "generated-flat-ambient-green-complexification-v1",
            "SOURCE_SHA": "0eae1b434ef037cae73995c530a79186e4041921",
            "ROOT": Path("/content/hrpoly-flat-ambient-green-complex"),
            "EVIDENCE": Path(
                "/content/hrpoly-flat-ambient-green-complex-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-flat-ambient-green-complex-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-flat-ambient-green-complex-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/"
                "BalabanCMP99SourceGeneratedFlatPhysicalAmbientGreenComplexification.lean":
                    "d1c95125790b2c62c1458737bbfe0912263d37c68c42bd49a0f57eed08b87cb5",
                "YangMills/RG/"
                "BalabanCMP99SourceGeneratedFlatPhysicalAmbientGreenComplexificationAudit.lean":
                    "10257b119f42801ba5eafe4d783d2123a1dc8342625308993a7dd18939f9b78c",
            },
            "QUEUE": [
                (
                    "generated_flat_ambient_green_complexification_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceGeneratedFlatPhysicalAmbientGreenComplexification",
                    ],
                    None,
                ),
                (
                    "generated_flat_ambient_green_complexification_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceGeneratedFlatPhysicalAmbientGreenComplexificationAudit.lean",
                    ],
                    4,
                ),
            ],
            "RECORDS": [],
        }
    )
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
