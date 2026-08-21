#!/usr/bin/env python3
"""Instrumental Colab gate for the localized coarse-field B0 brick C6b."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "8839c2378cec95793663b204661ed9b32c367dfd"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "5d2e9d6b0becc12cf83c7f88b930c4fa65eedb8f/"
    "scripts/colab_point_source_b0_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "7c313040630b20b47925615992b769d400a9a9ab3c7657cb3c165ec9df4ef621"
)
PARENT_RUNNER_PATH = Path("/content/colab_point_source_b0_validation.py")


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location("localized_field_b0_parent", PARENT_RUNNER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "localized-field-b0-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-localized-field-b0")
runner.EVIDENCE = Path("/content/hrpoly-localized-field-b0-evidence")
runner.ARCHIVE = Path("/content/hrpoly-localized-field-b0-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-localized-field-b0-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0.lean":
        "5a4ba9a215d46405601e5214a533c91b395be53ffecb37d836b96b8fdf7a9a84",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0Audit.lean":
        "6348789029a649db46da57aadd6142bbe1a386f18240cff17b2d98429d5566b4",
}
runner.QUEUE = [
    (
        "localized_field_b0_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0",
        ],
        None,
    ),
    (
        "localized_field_b0_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0Audit.lean",
        ],
        2,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
