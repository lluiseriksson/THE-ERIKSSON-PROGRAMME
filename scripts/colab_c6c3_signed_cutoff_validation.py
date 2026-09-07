#!/usr/bin/env python3
"""Instrumental Colab gate for the CMP96 C6c.3 signed cutoff species."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "abf69f4410c570c39525ccfd5a0a6a72c1caabbe"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "1572f8f3cbf915ce3e858efbcdc845c63c700c1b/"
    "scripts/colab_localized_field_b0_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "7039ee3cc0c22c3a6c10d7c59a3a9880ef22dc991d6fa7bc271cc35c66160e4a"
)
PARENT_RUNNER_PATH = Path("/content/colab_localized_field_b0_validation.py")


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location("c6c3_signed_cutoff_parent", PARENT_RUNNER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "c6c3-signed-cutoff-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6c3-signed-cutoff")
runner.EVIDENCE = Path("/content/hrpoly-c6c3-signed-cutoff-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6c3-signed-cutoff-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6c3-signed-cutoff-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacian.lean":
        "4a1b92b8d55ab28c47f9eae483cf46b8ff09a6cf892bd8887956f1befd41a52d",
    "YangMills/RG/BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacianAudit.lean":
        "a7d9438fad9d637b6c56d7492ea2231a7883a6f71c149d5b6ceb58df79650805",
}
runner.QUEUE = [
    (
        "c6c3_signed_cutoff_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacian",
        ],
        None,
    ),
    (
        "c6c3_signed_cutoff_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacianAudit.lean",
        ],
        4,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
