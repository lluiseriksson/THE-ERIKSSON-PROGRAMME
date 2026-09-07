#!/usr/bin/env python3
"""Instrumental Colab gate for the C6c.4a tilted inverse action."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "dab2c355e0b6e73f9c95fa5d4a8124bbf935e611"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "0565c88b098faaf1f7ec0028bd3c4ea807b14eec/"
    "scripts/colab_c6c3_signed_cutoff_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "f3ac422b63caa1535327e56f92840329a867e09b465fb1091e35f5f01e8e4b17"
)
PARENT_RUNNER_PATH = Path("/content/colab_c6c3_signed_cutoff_validation.py")


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "tilted_inverse_action_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "tilted-inverse-action-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-tilted-inverse-action")
runner.EVIDENCE = Path("/content/hrpoly-tilted-inverse-action-evidence")
runner.ARCHIVE = Path("/content/hrpoly-tilted-inverse-action-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-tilted-inverse-action-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/FinitePiLpTiltedInverseAction.lean":
        "86e81163807523b9dccbfee4714de852606314a7451f953a235e11bd860c0f78",
    "YangMills/RG/FinitePiLpTiltedInverseActionAudit.lean":
        "83897087a3c61671242c85124d08555f354fbb89a424fd3b775442aecb626032",
}
runner.QUEUE = [
    (
        "tilted_inverse_action_focal",
        ["lake", "build", "YangMills.RG.FinitePiLpTiltedInverseAction"],
        None,
    ),
    (
        "tilted_inverse_action_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/FinitePiLpTiltedInverseActionAudit.lean",
        ],
        1,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
