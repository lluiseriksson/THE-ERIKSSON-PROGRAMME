#!/usr/bin/env python3
"""Hash-gated Colab validation for finite PiLp outer complex transport."""

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
            "RUNNER_REV": "finite-pilp-complex-outer-transport-v1",
            "SOURCE_SHA": "5f13c04ae1b3bdb97fe17d25055f28509b2416ee",
            "ROOT": Path("/content/hrpoly-finite-pilp-complex-outer"),
            "EVIDENCE": Path(
                "/content/hrpoly-finite-pilp-complex-outer-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-finite-pilp-complex-outer-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-finite-pilp-complex-outer-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/"
                "FinitePiLpCanonicalComplexificationOuterTransport.lean":
                    "a3e6a28db47137db9a9ed6792a1bbe75fa7aae51058c9b216b0c5d5623c034aa",
                "YangMills/RG/"
                "FinitePiLpCanonicalComplexificationOuterTransportAudit.lean":
                    "25c248ec03123bc67fe67a79ad58bfbfed6e1feac1da135a3b74728a25b7bb31",
            },
            "QUEUE": [
                (
                    "finite_pilp_complex_outer_transport_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "FinitePiLpCanonicalComplexificationOuterTransport",
                    ],
                    None,
                ),
                (
                    "finite_pilp_complex_outer_transport_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "FinitePiLpCanonicalComplexificationOuterTransportAudit.lean",
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
