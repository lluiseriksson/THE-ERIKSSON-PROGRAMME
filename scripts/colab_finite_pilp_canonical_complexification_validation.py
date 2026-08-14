#!/usr/bin/env python3
"""Hash-gated Colab validation for canonical finite PiLp complexification."""

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
            "RUNNER_REV": "finite-pilp-canonical-complexification-v3",
            "SOURCE_SHA": "339d8f56da1d594ba6ef75adb8a975e5d3bb9e12",
            "ROOT": Path("/content/hrpoly-finite-pilp-complexification"),
            "EVIDENCE": Path(
                "/content/hrpoly-finite-pilp-complexification-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-finite-pilp-complexification-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-finite-pilp-complexification-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/FinitePiLpCanonicalComplexification.lean":
                    "f63b952cf9b7ed17ec588f8b1fcbff1b184e802be194a095bbf0bc40eeed07ef",
                "YangMills/RG/FinitePiLpCanonicalComplexificationAudit.lean":
                    "1f50d5911571e9b27f8b44ac2a10ed809ac2bd0a6fb1d385032caa96a0988927",
            },
            "QUEUE": [
                (
                    "finite_pilp_canonical_complexification_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG.FinitePiLpCanonicalComplexification",
                    ],
                    None,
                ),
                (
                    "finite_pilp_canonical_complexification_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "FinitePiLpCanonicalComplexificationAudit.lean",
                    ],
                    14,
                ),
            ],
            "RECORDS": [],
        }
    )
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
