#!/usr/bin/env python3
"""Colab gate for uniform point-source and localized-field source-flow B0."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "73bb1a2008c557840a91e50d8abe6b874947f7ee"
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
runner.RUNNER_REV = "source-flow-uniform-point-source-b0-v3"
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
        "8c1c1099dd5043a518df4a89b888548f894b9152a9e3fc85ecec3c9109a5d21e",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0Audit.lean":
        "743a914fd19d68a7aaeecaf61fee2c54e60a2c92ebb96f7d6851fcba37ca954d",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalLocalizedFieldB0.lean":
        "c083ff9c5693c8e3d35d9b6d7d58d7a0d2e95fd73b443401b9c19dcbf79109b1",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalLocalizedFieldB0Audit.lean":
        "377312d8a20be16f45434c7a70ecd32516fb5158032cfc50d1e18aa7a92d8bcb",
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
    (
        "source_flow_localized_field_b0_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalLocalizedFieldB0",
        ],
        None,
    ),
    (
        "source_flow_localized_field_b0_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalLocalizedFieldB0Audit.lean",
        ],
        2,
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
