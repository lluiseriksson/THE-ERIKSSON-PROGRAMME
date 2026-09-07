#!/usr/bin/env python3
"""Hash-gated Colab validation for the flat generated-background dictionary."""

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
            "RUNNER_REV": "flat-generated-background-dictionary-v1",
            "SOURCE_SHA": "b29a92d38504d8d9b282f14425b7d2a5d5237412",
            "ROOT": Path("/content/hrpoly-flat-generated-background-dictionary"),
            "EVIDENCE": Path(
                "/content/hrpoly-flat-generated-background-dictionary-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-flat-generated-background-dictionary-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-flat-generated-background-dictionary-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedBackgroundDictionary.lean":
                    "6e8000c1b8ef3fa5fe63ddf30a43ae97c1715843caa9686246d29e3e3819347b",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedBackgroundDictionaryAudit.lean":
                    "a772cc75aca79f454efb34cf6d52a5b683cca5a27b8d072ecf7652427e91813e",
            },
            "QUEUE": [
                (
                    "flat_generated_background_dictionary_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedBackgroundDictionary",
                    ],
                    None,
                ),
                (
                    "flat_generated_background_dictionary_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedBackgroundDictionaryAudit.lean",
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
