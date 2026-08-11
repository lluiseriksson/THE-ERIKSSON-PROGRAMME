#!/usr/bin/env python3
"""Hash-gated Colab validation for the direct generated-owner kernels.

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
            "RUNNER_REV": "flat-generated-qprime-direct-owner-kernel-v1",
            "SOURCE_SHA": "ac25a2e791b62048ab0de24714d691c8e17df1a4",
            "ROOT": Path("/content/hrpoly-flat-generated-qprime-direct-owner"),
            "EVIDENCE": Path(
                "/content/hrpoly-flat-generated-qprime-direct-owner-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-flat-generated-qprime-direct-owner-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-flat-generated-qprime-direct-owner-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel.lean":
                    "1c099d0bdb2094cebe25267c40208a06b5af57dfd668cdd12b4f0e2f4cac4cbd",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernelAudit.lean":
                    "2620fd7283532699b1af0a038a97c2f078127092512f81b36cfdd11522c2999b",
            },
            "QUEUE": [
                (
                    "flat_generated_qprime_direct_owner_kernel_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel",
                    ],
                    None,
                ),
                (
                    "flat_generated_qprime_direct_owner_kernel_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernelAudit.lean",
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
