#!/usr/bin/env python3
"""Hash-gated Colab validation for the generated/full-complex mass dictionary.

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
            "RUNNER_REV": "generated-qprime-mass-complex-coordinate-dictionary-v5",
            "SOURCE_SHA": "cace2db8b28a631f1a061ac2b23558e2681eb984",
            "ROOT": Path("/content/hrpoly-generated-qprime-mass-complex-dictionary"),
            "EVIDENCE": Path(
                "/content/hrpoly-generated-qprime-mass-complex-dictionary-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-generated-qprime-mass-complex-dictionary-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-generated-qprime-mass-complex-dictionary-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeMassComplexCoordinateDictionary.lean":
                    "2cf1cdbfb8731664384a989a9a60b58309d533811d272e94b5c667c0ef0c8f1a",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeMassComplexCoordinateDictionaryAudit.lean":
                    "8e408cbea90867f2b1a8d1572ae61767e7cbcf72c720cfdffec0a8fc3934edef",
            },
            "QUEUE": [
                (
                    "generated_qprime_mass_complex_coordinate_dictionary_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedQprimeMassComplexCoordinateDictionary",
                    ],
                    None,
                ),
                (
                    "generated_qprime_mass_complex_coordinate_dictionary_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedQprimeMassComplexCoordinateDictionaryAudit.lean",
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
