#!/usr/bin/env python3
"""Colab gate for the literal source-flow point-source B0 normal form."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "ba332c4e3cd21f672be064630ae6f8c7d2aaccd4"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "86e293e888d3fb1d553ead114357d94d17efafa1/"
    "scripts/colab_source_flow_source_owner_bound_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "b6e2d8b8c64590562525e639577d3cd6d30bedd9b5749aeacc69ac6b2cc02f09"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_source_owner_bound_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_point_source_b0_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-point-source-b0-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-point-source-b0")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-point-source-b0-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-point-source-b0-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-point-source-b0-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0.lean":
        "7d3fc852d84354547731d714a1d3b72c825e9e619065185d193ed65fcaea61f7",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0Audit.lean":
        "e5467a95379f8c375c4d6b6dd50d3c69dba8899c13f02089d2cd0e63d0b637e5",
}
runner.QUEUE = [
    (
        "source_flow_point_source_b0_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0",
        ],
        None,
    ),
    (
        "source_flow_point_source_b0_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0Audit.lean",
        ],
        3,
    ),
]


if __name__ == "__main__":
    real_unassign = None
    try:
        import importlib
        from google.colab import runtime

        runtime = importlib.reload(runtime)
        real_unassign = runtime.unassign
        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    code = runner.main()
    print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    try:
        from google.colab import files

        files.download(str(runner.ARCHIVE))
    except Exception as exc:
        print(
            "EVIDENCE_DOWNLOAD_STATUS=FAILED "
            + type(exc).__name__ + ": " + str(exc),
            flush=True,
        )
    print("RUNTIME_UNASSIGN_REQUESTED=1", flush=True)
    try:
        if real_unassign is not None:
            real_unassign()
    except Exception as exc:
        print(
            "RUNTIME_UNASSIGN_STATUS=FAILED "
            + type(exc).__name__ + ": " + str(exc),
            flush=True,
        )
    raise SystemExit(code)
