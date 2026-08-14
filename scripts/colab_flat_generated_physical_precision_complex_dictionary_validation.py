#!/usr/bin/env python3
"""Hash-gated Colab validation for the generated full precision dictionary."""

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
            "RUNNER_REV": "flat-generated-physical-precision-complex-v1",
            "SOURCE_SHA": "7456864edd66404496ae0a9eeaf332d2fc2bcbbb",
            "ROOT": Path("/content/hrpoly-flat-generated-physical-precision"),
            "EVIDENCE": Path(
                "/content/hrpoly-flat-generated-physical-precision-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-flat-generated-physical-precision-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-flat-generated-physical-precision-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedPhysicalPrecisionComplexDictionary.lean":
                    "016cdcc69f9b6dd1a8a2efb9c4a5056c86693c7db8ccdf2f827b8db50173f12f",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedPhysicalPrecisionComplexDictionaryAudit.lean":
                    "29655046dcede299612e6635f6b4ab62bafb00d5786db7277d9ef6c4a2baafc2",
            },
            "QUEUE": [
                (
                    "flat_generated_physical_precision_complex_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedPhysicalPrecisionComplexDictionary",
                    ],
                    None,
                ),
                (
                    "flat_generated_physical_precision_complex_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedPhysicalPrecisionComplexDictionaryAudit.lean",
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
