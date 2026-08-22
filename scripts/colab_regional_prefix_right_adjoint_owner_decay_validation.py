#!/usr/bin/env python3
"""Instrumental Colab gate for C6c.4d7 P8 right-adjoint owner decay."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "0ceff03b509c2b6c85c81631eff494e146719e50"
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
    "regional_prefix_right_adjoint_owner_decay_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "regional-prefix-right-adjoint-owner-decay-v3"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-regional-prefix-right-adjoint-owner-decay")
runner.EVIDENCE = Path(
    "/content/hrpoly-regional-prefix-right-adjoint-owner-decay-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-regional-prefix-right-adjoint-owner-decay-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-regional-prefix-right-adjoint-owner-decay-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixRightAdjointOwnerDecay.lean":
        "2c0761feda7e7da24db537b842b4a972f10087637e91e1c778626ab0c3a4630d",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixRightAdjointOwnerDecayAudit.lean":
        "d953a4d79bee36a820fb04ac611b8f779a1e98cc1baba9564dc64dcb4f70db14",
}
runner.QUEUE = [
    (
        "regional_prefix_right_adjoint_owner_decay_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixRightAdjointOwnerDecay",
        ],
        None,
    ),
    (
        "regional_prefix_right_adjoint_owner_decay_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixRightAdjointOwnerDecayAudit.lean",
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
