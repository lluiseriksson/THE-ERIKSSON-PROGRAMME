#!/usr/bin/env python3
"""Colab gate for the source-flow point-source zero-residue identity."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "5099e6f02d209f4503e2db04a4793048b4a5dcb5"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "458997896a5c37f0b22dce280389368f9ea880fd/"
    "scripts/colab_source_flow_zero_residue_aliasing_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "7de096a6f2ba7c750c7d3e2f96603ff32b9d110ffdc4c8b584140c6163522b87"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_zero_residue_aliasing_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_point_source_zero_residue_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-point-source-zero-residue-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-point-source-zero-residue")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-point-source-zero-residue-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-point-source-zero-residue-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-point-source-zero-residue-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceZeroResidue.lean":
        "16545f173048fdbaba1081fb300ca152a9b524c7b87d8f1da768793dc1a35004",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceZeroResidueAudit.lean":
        "b4a8a92348d693ab17514ddd8bb8d3406e60f440d139ebe1dd437cab4853bce9",
}
runner.QUEUE = [
    (
        "source_flow_point_source_zero_residue_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceZeroResidue",
        ],
        None,
    ),
    (
        "source_flow_point_source_zero_residue_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceZeroResidueAudit.lean",
        ],
        1,
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
