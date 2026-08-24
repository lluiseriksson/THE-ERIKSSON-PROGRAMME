#!/usr/bin/env python3
"""Colab gate for the depth-uniform literal source-flow point-source B0."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "c65d00097e72a3b41022b521b2754f8fe8328eb4"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "602ab7a3054e1caabd09cccb25beaee11c3f188e/"
    "scripts/colab_source_flow_point_source_b0_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "3b48613bfc798ac20437ccbad4c555cb051c15186c5e141af84bb3125b554260"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_point_source_b0_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_uniform_point_source_b0_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-uniform-point-source-b0-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-uniform-point-source-b0")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-uniform-point-source-b0-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-uniform-point-source-b0-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-uniform-point-source-b0-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0.lean":
        "8e563c07ed1c7c6681813edf8eb72121689686473b13f074c83ff11f9b65ba98",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0Audit.lean":
        "743a914fd19d68a7aaeecaf61fee2c54e60a2c92ebb96f7d6851fcba37ca954d",
}
runner.QUEUE = [
    (
        "source_flow_uniform_point_source_b0_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0",
        ],
        None,
    ),
    (
        "source_flow_uniform_point_source_b0_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0Audit.lean",
        ],
        5,
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
