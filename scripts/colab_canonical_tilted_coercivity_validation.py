#!/usr/bin/env python3
"""Instrumental Colab gate for C6c.4b canonical tilted coercivity."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "4d81940604d80b9534aa2a6cc7e433593d7db691"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "b56754ee4c02f5c54738da28a54952fe78999635/"
    "scripts/colab_tilted_inverse_action_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "e9e0c0699faae40edb9376fb5a1b2d42095935483752b86683ed222827db02bf"
)
PARENT_RUNNER_PATH = Path("/content/colab_tilted_inverse_action_validation.py")


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "canonical_tilted_coercivity_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "canonical-tilted-coercivity-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-canonical-tilted-coercivity")
runner.EVIDENCE = Path("/content/hrpoly-canonical-tilted-coercivity-evidence")
runner.ARCHIVE = Path("/content/hrpoly-canonical-tilted-coercivity-evidence.tar.gz")
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-canonical-tilted-coercivity-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/FinitePiLpExponentialInverseDecay.lean":
        "0a9a90ac457c8e722d6186d74042cb8712eafd9b31f65d44332001277ebf5b99",
    "YangMills/RG/FinitePiLpExponentialInverseDecayAudit.lean":
        "4ffe84cf3fe7b06e6203e6a21ae9f68c6dd14a8f821b7ccfc9795919195752d8",
}
runner.QUEUE = [
    (
        "canonical_tilted_coercivity_focal",
        [
            "lake", "build",
            "YangMills.RG.FinitePiLpExponentialInverseDecay",
        ],
        None,
    ),
    (
        "canonical_tilted_coercivity_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/FinitePiLpExponentialInverseDecayAudit.lean",
        ],
        4,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
