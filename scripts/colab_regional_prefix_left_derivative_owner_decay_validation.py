#!/usr/bin/env python3
"""Instrumental Colab gate for C6c.4d4 P8 left-derivative decay."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "957b45f7944ed90bc71aaf63d922e97efee32cf6"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "2239528498da8413b4fd5adb64e84b0bc7a3dd7b/"
    "scripts/colab_regional_prefix_rescaled_owner_decay_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "f53a5636631f73c2f2e59b030767b4a24658dc33b28ad79782462e333bbae656"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_rescaled_owner_decay_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "regional_prefix_left_derivative_owner_decay_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "regional-prefix-left-derivative-owner-decay-v3"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-regional-prefix-left-derivative-owner-decay")
runner.EVIDENCE = Path(
    "/content/hrpoly-regional-prefix-left-derivative-owner-decay-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-regional-prefix-left-derivative-owner-decay-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-regional-prefix-left-derivative-owner-decay-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixLeftDerivativeOwnerDecay.lean":
        "c97ceee3da508411bf08342207196179ff7ece6ae6c7643887c7a4772feeff6e",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixLeftDerivativeOwnerDecayAudit.lean":
        "2de7ca9a542cda1eba29560edf39a5610e100f1ba6d6897edefa4ceb8081f116",
}
runner.QUEUE = [
    (
        "regional_prefix_left_derivative_owner_decay_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixLeftDerivativeOwnerDecay",
        ],
        None,
    ),
    (
        "regional_prefix_left_derivative_owner_decay_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixLeftDerivativeOwnerDecayAudit.lean",
        ],
        2,
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
