#!/usr/bin/env python3
"""Hash-gated Colab validation for the generated terminal-block collapse.

This instrumentation-only wrapper specializes the sealed generic fresh-clone
runner to one immutable PRE-VALIDATION source checkpoint and its two exact Git
blobs.  It does not alter the mathematical source under validation.
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
            "RUNNER_REV": "generated-terminal-block-collapse-v1",
            "SOURCE_SHA": "875ad1e89983a510c6d4243121da324e0b66af79",
            "ROOT": Path("/content/hrpoly-generated-terminal-block-collapse"),
            "EVIDENCE": Path(
                "/content/hrpoly-generated-terminal-block-collapse-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-generated-terminal-block-collapse-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-generated-terminal-block-collapse-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse.lean":
                    "d3158b84f95ab165675106c4f7868a963d4bc372eb5fab263f4c2b63f4ac49ac",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedTerminalBlockCollapseAudit.lean":
                    "51aef4f0cffb34b58a9a14400d35c1b3cb5d2d34c16a23cbc9c6cf42852e2729",
            },
            "QUEUE": [
                (
                    "generated_terminal_block_collapse_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse",
                    ],
                    None,
                ),
                (
                    "generated_terminal_block_collapse_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedTerminalBlockCollapseAudit.lean",
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
