#!/usr/bin/env python3
"""Instrumental Colab gate for the named point-source B0 brick C6a."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "1f53807c6040a0856ca98e49f610d40d6b28fed7"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "003cd61e3624fa852a2525e36ce661e745b8bf7f/"
    "scripts/colab_source_owner_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "53974a787a5a15b1af36208b501c7f4bd43c147ba6d49b8a49d77ea6dcbe91e3"
)
PARENT_RUNNER_PATH = Path("/content/colab_source_owner_validation.py")


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location("point_source_b0_parent", PARENT_RUNNER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "point-source-b0-v2-zero-weight-normalization"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-point-source-b0")
runner.EVIDENCE = Path("/content/hrpoly-point-source-b0-evidence")
runner.ARCHIVE = Path("/content/hrpoly-point-source-b0-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-point-source-b0-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceB0.lean":
        "07f0173fdd9a789f30c380fbc9fb803264d5b0d47c5ea009aca6870450ea551c",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceB0Audit.lean":
        "aeb47cce27a4101c55a136ef762c713b0979778762d383adb2cc379d7009a205",
}
runner.QUEUE = [
    (
        "point_source_b0_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceB0",
        ],
        None,
    ),
    (
        "point_source_b0_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceB0Audit.lean",
        ],
        3,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
