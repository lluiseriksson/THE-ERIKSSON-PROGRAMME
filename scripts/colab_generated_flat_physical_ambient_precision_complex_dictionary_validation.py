#!/usr/bin/env python3
"""Hash-gated Colab validation for the exact Step-7b ambient dictionary."""

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
            "RUNNER_REV": "generated-flat-ambient-precision-step7b-dictionary-v3",
            "SOURCE_SHA": "6ae54d1a5a0a179cd2cf3ff4a5b89bfe35fc9aee",
            "ROOT": Path("/content/hrpoly-step7b-ambient-precision"),
            "EVIDENCE": Path(
                "/content/hrpoly-step7b-ambient-precision-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-step7b-ambient-precision-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-step7b-ambient-precision-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/"
                "BalabanCMP99SourceGeneratedFlatPhysicalAmbientPrecisionComplexDictionary.lean":
                    "b6648fc79b81b32cf5bb53701d27400aba61f8feeb2aa9e30cf99ed7151aee58",
                "YangMills/RG/"
                "BalabanCMP99SourceGeneratedFlatPhysicalAmbientPrecisionComplexDictionaryAudit.lean":
                    "43ce7b06a054c2401a6cf8d07ea9d89d449212eba1fe02a6fe1bae9b8453c78f",
            },
            "QUEUE": [
                (
                    "generated_flat_ambient_precision_step7b_dictionary_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceGeneratedFlatPhysicalAmbientPrecisionComplexDictionary",
                    ],
                    None,
                ),
                (
                    "generated_flat_ambient_precision_step7b_dictionary_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceGeneratedFlatPhysicalAmbientPrecisionComplexDictionaryAudit.lean",
                    ],
                    8,
                ),
            ],
            "RECORDS": [],
        }
    )
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
