#!/usr/bin/env python3
"""Hash-gated Colab validation for the generated complex stencil dictionary."""

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
            "RUNNER_REV": "flat-generated-complex-stencil-v5",
            "SOURCE_SHA": "68de67d6e2d3887c4c7587603d0d615a494df840",
            "ROOT": Path("/content/hrpoly-flat-generated-complex-stencil"),
            "EVIDENCE": Path(
                "/content/hrpoly-flat-generated-complex-stencil-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-flat-generated-complex-stencil-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-flat-generated-complex-stencil-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedComplexStencilDictionary.lean":
                    "1de69ea0b85000de633ce1c4ace0c616e780bbcff55f6a98660450c908a92356",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedComplexStencilDictionaryAudit.lean":
                    "0a34ba42e5e5e5b8d6e331a55f38f07c07e9cc3fb2729f2efca974ce96ae13b6",
            },
            "QUEUE": [
                (
                    "flat_generated_complex_stencil_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedComplexStencilDictionary",
                    ],
                    None,
                ),
                (
                    "flat_generated_complex_stencil_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedComplexStencilDictionaryAudit.lean",
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
