#!/usr/bin/env python3
"""Instrumental Colab gate for the C6c.4c one-owner tilted input."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "b65846a238d3e58943950ad4ee78073dd1d994dd"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "90e146de6277f809dd2941862667ec9ef4dc109d/"
    "scripts/colab_canonical_tilted_coercivity_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "fc833b579a8505e78288ac3781af5fe1fa09982c6f5f8baf4b9e5c62fc9979a3"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_canonical_tilted_coercivity_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_owner_tilted_input_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-owner-tilted-input-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-owner-tilted-input")
runner.EVIDENCE = Path("/content/hrpoly-source-owner-tilted-input-evidence")
runner.ARCHIVE = Path("/content/hrpoly-source-owner-tilted-input-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-source-owner-tilted-input-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99Eq342SourceOwnerTiltedInput.lean":
        "b2985ea2757d5dbaccd75c644430f105f3acc8b5cc629a8dbabf3e6db47fc1e0",
    "YangMills/RG/BalabanCMP99Eq342SourceOwnerTiltedInputAudit.lean":
        "fb5de2f1dca5fb952d7b855a03925be941ad13c1fcc71c8968fbab809356b6ed",
}
runner.QUEUE = [
    (
        "source_owner_tilted_input_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq342SourceOwnerTiltedInput",
        ],
        None,
    ),
    (
        "source_owner_tilted_input_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99Eq342SourceOwnerTiltedInputAudit.lean",
        ],
        2,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
