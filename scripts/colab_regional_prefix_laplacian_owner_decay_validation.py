#!/usr/bin/env python3
"""Instrumental Colab gate for C6c.4d6 P8 Laplacian owner decay."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "df6dbb9e89454e1b49129d9cdd4a878e2af79f68"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "26078282adad34a477ad7ab79649d49a14558b41/"
    "scripts/colab_regional_prefix_green_block_owner_decay_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "1e239ab30d12aca72d4c3b89623fd177fcd0a2e3001d57d9d391f41fcf7faa8e"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_green_block_owner_decay_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "regional_prefix_laplacian_owner_decay_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "regional-prefix-laplacian-owner-decay-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-regional-prefix-laplacian-owner-decay")
runner.EVIDENCE = Path(
    "/content/hrpoly-regional-prefix-laplacian-owner-decay-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-regional-prefix-laplacian-owner-decay-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-regional-prefix-laplacian-owner-decay-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixLaplacianOwnerDecay.lean":
        "a32312d7c41bff040bb9a4708d8ff68f9d39af1e6e3b0fe82a37c00a4faf0515",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixLaplacianOwnerDecayAudit.lean":
        "bdb5a594f028e9a3bafc2f3cb5b5b1887847d07415cc2bf8d9f574db9fd1eab4",
}
runner.QUEUE = [
    (
        "regional_prefix_laplacian_owner_decay_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixLaplacianOwnerDecay",
        ],
        None,
    ),
    (
        "regional_prefix_laplacian_owner_decay_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixLaplacianOwnerDecayAudit.lean",
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
