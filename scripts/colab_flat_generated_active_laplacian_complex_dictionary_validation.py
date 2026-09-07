#!/usr/bin/env python3
"""Hash-gated Colab validation for the generated active Laplacian dictionary."""

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
            "RUNNER_REV": "flat-generated-active-laplacian-complex-v1",
            "SOURCE_SHA": "e123abc98f29b916a7659e4b1520fc0f92779ab5",
            "ROOT": Path("/content/hrpoly-flat-generated-active-laplacian"),
            "EVIDENCE": Path(
                "/content/hrpoly-flat-generated-active-laplacian-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-flat-generated-active-laplacian-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-flat-generated-active-laplacian-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedActiveLaplacianComplexDictionary.lean":
                    "3795e3c07595d50ec494b9489f08bfb5c18b4f93bfc5f854fcf273ef00aa1ff3",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedActiveLaplacianComplexDictionaryAudit.lean":
                    "9492e48f8f088932d754ba1c6ebd2e88dbac4919d6afe5e2d5251e94c8b9cb46",
            },
            "QUEUE": [
                (
                    "flat_generated_active_laplacian_complex_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedActiveLaplacianComplexDictionary",
                    ],
                    None,
                ),
                (
                    "flat_generated_active_laplacian_complex_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedActiveLaplacianComplexDictionaryAudit.lean",
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
