#!/usr/bin/env python3
"""Instrumental Colab gate for source-localization owner transport C5."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "d8b873a4abf6d83bdf57068ff850a90335974f40"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "5cc5ea8c2467f7e60d263233a642449a3860693d/"
    "scripts/colab_source_point_owner_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "233e3e0c33034bafe2cc41352231f54ab2536f2d65edf70b7ada4a78673368ca"
)
PARENT_RUNNER_PATH = Path("/content/colab_source_point_owner_validation.py")


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location("source_owner_parent", PARENT_RUNNER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-owner-transport-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-owner")
runner.EVIDENCE = Path("/content/hrpoly-source-owner-evidence")
runner.ARCHIVE = Path("/content/hrpoly-source-owner-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-source-owner-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalSourceOwnerBound.lean":
        "898be703002fd1ae58f8f9d34c12ba4188bc47233c1013477ead53351ca24a38",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalSourceOwnerBoundAudit.lean":
        "074ee48b97cca400e9399163b6d150ae4950df939cbced4e84e9e47107dafc58",
}
runner.QUEUE = [
    (
        "source_owner_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalSourceOwnerBound",
        ],
        None,
    ),
    (
        "source_owner_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalSourceOwnerBoundAudit.lean",
        ],
        1,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
