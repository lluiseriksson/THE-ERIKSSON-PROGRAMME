#!/usr/bin/env python3
"""Hash-gated Colab validation for the flat generated physical precision.

This is an instrumentation-only wrapper around the sealed generic fresh-clone
runner.  It changes only the immutable source checkpoint, exact Git-blob
hashes, paths and focal queue.  The mathematical source remains the parent
PRE-VALIDATION checkpoint.
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
            "RUNNER_REV": "generated-flat-physical-precision-kernel-v3",
            "SOURCE_SHA": "277d949effcbabad416e7ee4a353ab34a5df8cc7",
            "ROOT": Path("/content/hrpoly-generated-flat-physical-precision"),
            "EVIDENCE": Path(
                "/content/hrpoly-generated-flat-physical-precision-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-generated-flat-physical-precision-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-generated-flat-physical-precision-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPrecisionKernel.lean":
                    "62bf6a08dfa4a68161d484966ed6beaa51d9859edfdf0c1558fb22715b779c39",
                "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPrecisionKernelAudit.lean":
                    "d58320d9d1412d650eb872deecfecb6ac46db9746933e81d3fdeecd76267910d",
            },
            "QUEUE": [
                (
                    "generated_flat_physical_precision_kernel_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceGeneratedFlatPhysicalPrecisionKernel",
                    ],
                    None,
                ),
                (
                    "generated_flat_physical_precision_kernel_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceGeneratedFlatPhysicalPrecisionKernelAudit.lean",
                    ],
                    5,
                ),
            ],
            "RECORDS": [],
        }
    )
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
