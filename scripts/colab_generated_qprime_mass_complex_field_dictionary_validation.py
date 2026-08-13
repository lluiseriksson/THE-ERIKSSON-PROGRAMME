#!/usr/bin/env python3
"""Hash-gated Colab validation for the generated complex mass field dictionary.

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
            "RUNNER_REV": "generated-qprime-mass-complex-field-dictionary-v1",
            "SOURCE_SHA": "46ef9dc63b7c84919d458ec57358e64d669712e2",
            "ROOT": Path("/content/hrpoly-generated-qprime-mass-complex-field"),
            "EVIDENCE": Path(
                "/content/hrpoly-generated-qprime-mass-complex-field-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-generated-qprime-mass-complex-field-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-generated-qprime-mass-complex-field-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeMassComplexFieldDictionary.lean":
                    "3e9992bb61753ade8ea73f47c65e51b2a6866f8fef7e891336610404b12c0cd0",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeMassComplexFieldDictionaryAudit.lean":
                    "c9c9380b94ef9951d87e3f686924528a31317502133e8728b799ea0853e60ae7",
            },
            "QUEUE": [
                (
                    "generated_qprime_mass_complex_field_dictionary_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedQprimeMassComplexFieldDictionary",
                    ],
                    None,
                ),
                (
                    "generated_qprime_mass_complex_field_dictionary_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedQprimeMassComplexFieldDictionaryAudit.lean",
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
