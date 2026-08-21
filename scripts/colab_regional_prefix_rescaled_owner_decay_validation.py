#!/usr/bin/env python3
"""Instrumental Colab gate for C6c.4d3 rescaled owner Green decay."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "0f72fefe09c24aaf5ac998f25032d70fbc0e4630"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "f4aa3e3bba797e915aef1cca2ae5021d28ca4b03/"
    "scripts/colab_regional_prefix_owner_decay_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "0fcaa1a0e861d10b014f4e60e62971c3b48241496dfcef8e75294bff86cfd4a9"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_owner_decay_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "regional_prefix_rescaled_owner_decay_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "regional-prefix-rescaled-owner-decay-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-regional-prefix-rescaled-owner-decay")
runner.EVIDENCE = Path(
    "/content/hrpoly-regional-prefix-rescaled-owner-decay-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-regional-prefix-rescaled-owner-decay-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-regional-prefix-rescaled-owner-decay-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixRescaledOwnerDecay.lean":
        "b85c7e916776efd175247dccdbc84ccb496810d7a3c072459537392707868acf",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixRescaledOwnerDecayAudit.lean":
        "f362bd316fc5f08d829b91d72460c85f64f093950eb6ee9f2e1db5eddb22e04c",
}
runner.QUEUE = [
    (
        "regional_prefix_rescaled_owner_decay_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixRescaledOwnerDecay",
        ],
        None,
    ),
    (
        "regional_prefix_rescaled_owner_decay_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixRescaledOwnerDecayAudit.lean",
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
