#!/usr/bin/env python3
"""Instrumental Colab gate for C6c.4d0 physical P8 tilted coercivity."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "eb9667ca6234ce92c33cfaf2e02054890519e042"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "228f45bf7a8f75259d1d4af29876e4b60d399e9e/"
    "scripts/colab_source_owner_tilted_input_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "7d2c3af7b4f903b3ba23ea8d83cf7f226b77a432d36c4bf43a055dfcce8f048b"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_owner_tilted_input_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "regional_prefix_tilted_coercivity_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "regional-prefix-tilted-coercivity-v2"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-regional-prefix-tilted-coercivity")
runner.EVIDENCE = Path(
    "/content/hrpoly-regional-prefix-tilted-coercivity-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-regional-prefix-tilted-coercivity-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-regional-prefix-tilted-coercivity-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixTiltedCoercivity.lean":
        "527501c48691fdfaa58ecaa7d90dfe55b69c415df0b86594a31051cf86a2dd4c",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixTiltedCoercivityAudit.lean":
        "336a262ee3a17a6c08eb6d7178d73c545bf955f8529e4dd12a9bbbd74401a25b",
}
runner.QUEUE = [
    (
        "regional_prefix_tilted_coercivity_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixTiltedCoercivity",
        ],
        None,
    ),
    (
        "regional_prefix_tilted_coercivity_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixTiltedCoercivityAudit.lean",
        ],
        1,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
