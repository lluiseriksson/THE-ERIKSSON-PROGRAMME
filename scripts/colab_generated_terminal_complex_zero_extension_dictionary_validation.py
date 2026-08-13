#!/usr/bin/env python3
"""Hash-gated Colab validation for the generated zero-extension dictionary.

This instrumentation-only wrapper specializes the generic fresh-clone runner
to one immutable PRE-VALIDATION source checkpoint and its two exact Git blobs.
It does not alter the mathematical source under validation.
"""

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
            "RUNNER_REV": "generated-terminal-complex-zero-extension-dictionary-v1",
            "SOURCE_SHA": "4e17bd3f073f97227b7268c98500e4de63e96e53",
            "ROOT": Path("/content/hrpoly-generated-complex-zero-extension"),
            "EVIDENCE": Path(
                "/content/hrpoly-generated-complex-zero-extension-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-generated-complex-zero-extension-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-generated-complex-zero-extension-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedTerminalComplexZeroExtensionDictionary.lean":
                    "5df8605fbd752112969b0dd88ac8e6b60aa03e5749330faee3257c3f6bb988d2",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedTerminalComplexZeroExtensionDictionaryAudit.lean":
                    "03f2c214024eeb588fa139ab8ec4b515f0f5b0d8567d00441613b7cae3099343",
            },
            "QUEUE": [
                (
                    "generated_terminal_complex_zero_extension_dictionary_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedTerminalComplexZeroExtensionDictionary",
                    ],
                    None,
                ),
                (
                    "generated_terminal_complex_zero_extension_dictionary_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedTerminalComplexZeroExtensionDictionaryAudit.lean",
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
