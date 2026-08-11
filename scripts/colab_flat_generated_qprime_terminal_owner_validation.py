#!/usr/bin/env python3
"""Hash-gated Colab validation for the flat generated terminal-owner action.

This is an instrumentation-only wrapper around the previously sealed generic
fresh-clone runner.  It changes only the immutable source checkpoint, exact
Git-blob hashes, paths and focal queue.  The mathematical source remains the
parent PRE-VALIDATION checkpoint.
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
            "RUNNER_REV": "flat-generated-qprime-terminal-owner-v2",
            "SOURCE_SHA": "d89463586c883709e432c088156819d19bc12423",
            "ROOT": Path("/content/hrpoly-flat-generated-qprime-terminal-owner"),
            "EVIDENCE": Path(
                "/content/hrpoly-flat-generated-qprime-terminal-owner-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-flat-generated-qprime-terminal-owner-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-flat-generated-qprime-terminal-owner-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeTerminalOwner.lean":
                    "bc71f397fe5954f13369ec60ed761dd35e516018e3ba3962fca715b7980d0b29",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeTerminalOwnerAudit.lean":
                    "269e9fe2eaa8785721d391670197a22b56c0b881df4ca5597ff6a284b9acd304",
            },
            "QUEUE": [
                (
                    "flat_generated_qprime_terminal_owner_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeTerminalOwner",
                    ],
                    None,
                ),
                (
                    "flat_generated_qprime_terminal_owner_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedQprimeTerminalOwnerAudit.lean",
                    ],
                    4,
                ),
            ],
            "RECORDS": [],
        }
    )
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
