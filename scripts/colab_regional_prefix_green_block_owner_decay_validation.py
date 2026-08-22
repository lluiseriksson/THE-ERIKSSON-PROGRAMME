#!/usr/bin/env python3
"""Instrumental Colab gate for C6c.4d5 P8 Green owner decay."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "c3d8d338e3bea4f378cca59f5767c616c316feba"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "74496bd2d6bce35c4a3c683a74144f90acd2532c/"
    "scripts/colab_regional_prefix_left_derivative_owner_decay_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "389d1cbe1a4d4e9dc3967db803c77f90fd8060852f68ce410739ba476f5931fa"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_left_derivative_owner_decay_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "regional_prefix_green_block_owner_decay_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "regional-prefix-green-block-owner-decay-v2"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-regional-prefix-green-block-owner-decay")
runner.EVIDENCE = Path(
    "/content/hrpoly-regional-prefix-green-block-owner-decay-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-regional-prefix-green-block-owner-decay-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-regional-prefix-green-block-owner-decay-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixGreenBlockLocalizedOwnerDecay.lean":
        "7ac800973ad7bbe3b6b2eeb979b082c7d91141b38a7123818e54d2c732882f09",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixGreenBlockLocalizedOwnerDecayAudit.lean":
        "8c45b8009781c28336dc97e107daa7fa36f1bea5718eb7315ac6375e643772d1",
}
runner.QUEUE = [
    (
        "regional_prefix_green_block_owner_decay_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixGreenBlockLocalizedOwnerDecay",
        ],
        None,
    ),
    (
        "regional_prefix_green_block_owner_decay_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixGreenBlockLocalizedOwnerDecayAudit.lean",
        ],
        1,
    ),
]


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    code = runner.main()
    try:
        from google.colab import files

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(code)
