#!/usr/bin/env python3
"""Instrumental Colab gate for C6c.4d1 P8 owner-input Green action."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "93a4f664febe371aff82d2d67b4e31b665db47a0"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "35eae7069e6019e5f321a650d06f01cf41254e1d/"
    "scripts/colab_regional_prefix_tilted_coercivity_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "766d62690f60c5dd01fc33d2d2d2722a1fc005cac93476f2f4f58ace1607a678"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_tilted_coercivity_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "regional_prefix_owner_input_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "regional-prefix-owner-input-action-v2"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-regional-prefix-owner-input")
runner.EVIDENCE = Path("/content/hrpoly-regional-prefix-owner-input-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-regional-prefix-owner-input-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-regional-prefix-owner-input-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixOwnerInputAction.lean":
        "7e18412f7ad96b7769ea90dba12debc6899c14708b133308a8f4e632be4f5097",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixOwnerInputActionAudit.lean":
        "4e78ac70adb0c1b65ef80734bad81c36e9645b21a2d030947a1370be14f2976e",
}
runner.QUEUE = [
    (
        "regional_prefix_owner_input_action_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixOwnerInputAction",
        ],
        None,
    ),
    (
        "regional_prefix_owner_input_action_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixOwnerInputActionAudit.lean",
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
