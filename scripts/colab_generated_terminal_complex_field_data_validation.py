#!/usr/bin/env python3
"""Hash-gated Colab validation for generated terminal complex field data.

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
            "RUNNER_REV": "generated-terminal-complex-field-data-v3",
            "SOURCE_SHA": "44d4de580d0be52e0a9a45e74e8ad90b85ca0b4c",
            "ROOT": Path("/content/hrpoly-generated-complex-field-data"),
            "EVIDENCE": Path(
                "/content/hrpoly-generated-complex-field-data-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-generated-complex-field-data-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-generated-complex-field-data-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedTerminalComplexFieldData.lean":
                    "85d7ac16d799e8f8dafe33e111aece43a5106a88db3355318d4ec1d22b2c0402",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedTerminalComplexFieldDataAudit.lean":
                    "0aa8cb34ce0a8566348d1f48eb2d1b44d33dc1952665be8f0bff273f601eb4cd",
            },
            "QUEUE": [
                (
                    "generated_terminal_complex_field_data_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedTerminalComplexFieldData",
                    ],
                    None,
                ),
                (
                    "generated_terminal_complex_field_data_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedTerminalComplexFieldDataAudit.lean",
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
