#!/usr/bin/env python3
"""Hash-gated Colab validation for the full-box Qprime mass kernel.

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
            "RUNNER_REV": "full-complex-qprime-mass-coordinate-kernel-v1",
            "SOURCE_SHA": "99c56a599ac3b0eeba2bfc64c3721717ed8e8311",
            "ROOT": Path("/content/hrpoly-full-complex-qprime-mass-kernel"),
            "EVIDENCE": Path(
                "/content/hrpoly-full-complex-qprime-mass-kernel-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-full-complex-qprime-mass-kernel-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-full-complex-qprime-mass-kernel-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatFullComplexQprimeMassCoordinateKernel.lean":
                    "92d8cadfde3295b73884d2aca56ea9ef80b1756a5a0f4d2eb6ea1a730093ceaa",
                "YangMills/RG/BalabanCMP99SourceFlatFullComplexQprimeMassCoordinateKernelAudit.lean":
                    "17792b2979093492a2fef9658cafbddc7eb8d42da4624e32c95cdb7ba10ffb9f",
            },
            "QUEUE": [
                (
                    "full_complex_qprime_mass_coordinate_kernel_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatFullComplexQprimeMassCoordinateKernel",
                    ],
                    None,
                ),
                (
                    "full_complex_qprime_mass_coordinate_kernel_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatFullComplexQprimeMassCoordinateKernelAudit.lean",
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
