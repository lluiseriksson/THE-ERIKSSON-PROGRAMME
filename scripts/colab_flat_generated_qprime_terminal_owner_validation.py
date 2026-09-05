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

    repro = Path("/content/terminal-owner-power-repro.lean")
    repro.write_text(
        """import Mathlib

noncomputable section

example {n depth : ℕ} (weight : ℝ)
    (v : EuclideanSpace ℝ (Fin (n - 1))) :
    weight ^ depth • (weight • v) = weight ^ (depth + 1) • v := by
  simpa only [smul_smul] using
    congrArg (fun scalar : ℝ => scalar • v) (pow_succ weight depth).symm
""",
        encoding="utf-8",
    )

    namespace: dict[str, object] = {"__name__": "colab_validation_base"}
    exec(compile(base_source, BASE_RUNNER_URL, "exec"), namespace)
    namespace.update(
        {
            "RUNNER_REV": "flat-generated-qprime-terminal-owner-v5",
            "SOURCE_SHA": "e781ba4a25bea54229a3679bc1af50536a42a2e2",
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
                    "b1bdc994ba63edd4f2f9f048e897ba18d629264dfc52855539e7b631a7116193",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeTerminalOwnerAudit.lean":
                    "269e9fe2eaa8785721d391670197a22b56c0b881df4ca5597ff6a284b9acd304",
            },
            "QUEUE": [
                (
                    "terminal_owner_power_repro",
                    ["lake", "env", "lean", str(repro)],
                    None,
                ),
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
