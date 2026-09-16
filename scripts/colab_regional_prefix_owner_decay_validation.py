#!/usr/bin/env python3
"""Instrumental Colab gate for C6c.4d2 owner-distance Green decay."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "3ab0cf18587b71b54ac9bb33797316214ad8b0e9"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "8cfe88fb6c4017dcf21ba3f07962b9d63b26c2df/"
    "scripts/colab_regional_prefix_owner_input_action_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "d02aa0b9bba6dd82f5a8c4641ef6b50dbd5264abc4528a9948cea07a2b2ea5e7"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_owner_input_action_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "regional_prefix_owner_decay_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "regional-prefix-owner-decay-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-regional-prefix-owner-decay")
runner.EVIDENCE = Path("/content/hrpoly-regional-prefix-owner-decay-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-regional-prefix-owner-decay-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-regional-prefix-owner-decay-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixOwnerDecay.lean":
        "b2f88bb72c6c81f579891e50719304837f88c19b68bd45f26128475ec17899ea",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixOwnerDecayAudit.lean":
        "e3d46730e942b9922ce21c2fd0a3470bcb49743b0c9b577ff0516ae8de2aae6c",
}
runner.QUEUE = [
    (
        "regional_prefix_owner_decay_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixOwnerDecay",
        ],
        None,
    ),
    (
        "regional_prefix_owner_decay_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixOwnerDecayAudit.lean",
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
