#!/usr/bin/env python3
"""Hash-gated Colab validation for the generated precision scalar dictionary.

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
            "RUNNER_REV": "generated-precision-scalar-dictionary-v1",
            "SOURCE_SHA": "e0692ca78b4d3502226f441c8e61d40c8fa442d1",
            "ROOT": Path("/content/hrpoly-generated-precision-scalar-dictionary"),
            "EVIDENCE": Path(
                "/content/hrpoly-generated-precision-scalar-dictionary-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-generated-precision-scalar-dictionary-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-generated-precision-scalar-dictionary-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedPrecisionScalarDictionary.lean":
                    "ae65df51d12fc64d8ed3823c6f58718e6a05e0c90ea5f8492fcfafd2e0dc560b",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedPrecisionScalarDictionaryAudit.lean":
                    "a6f62a251479ae3fb2131c7b4dd909bda634860f38cc8e288d1f6bc44dfaaa48",
            },
            "QUEUE": [
                (
                    "generated_precision_scalar_dictionary_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedPrecisionScalarDictionary",
                    ],
                    None,
                ),
                (
                    "generated_precision_scalar_dictionary_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedPrecisionScalarDictionaryAudit.lean",
                    ],
                    6,
                ),
            ],
            "RECORDS": [],
        }
    )
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
