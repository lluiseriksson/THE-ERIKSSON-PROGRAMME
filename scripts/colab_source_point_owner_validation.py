#!/usr/bin/env python3
"""Instrumental Colab gate for the generated point-source owner bound.

The wrapper reuses the already measured deterministic package-materialization
runner and changes only the exact source checkpoint, blob gates and focal
queue.  The imported runner is itself fetched by immutable Git SHA and
verified before execution.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "cb78e9f491d04b2e3578d5da57d7cd66976354b7"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bbd83565af5be389c997889bbea36e162bf2c68c/"
    "scripts/colab_source_fine_to_coarse_owner_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "e7bf2973a3274e60456081cbef7daacd34944e2915992e9f782807138518069f"
)
PARENT_RUNNER_PATH = Path("/content/colab_source_fine_to_coarse_owner_validation.py")


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location("point_owner_parent", PARENT_RUNNER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-point-owner-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-point-owner")
runner.EVIDENCE = Path("/content/hrpoly-source-point-owner-evidence")
runner.ARCHIVE = Path("/content/hrpoly-source-point-owner-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-source-point-owner-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBound.lean":
        "70842c878e6223ebbedf88f230e76644b99d106ad6bbaea98f77e5e539ad13f2",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBoundAudit.lean":
        "4d618354addaa277296e1115a3e2323598cf2915703a07341993f6fd207d0bd5",
}
runner.QUEUE = [
    (
        "point_owner_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBound",
        ],
        None,
    ),
    (
        "point_owner_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBoundAudit.lean",
        ],
        2,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
