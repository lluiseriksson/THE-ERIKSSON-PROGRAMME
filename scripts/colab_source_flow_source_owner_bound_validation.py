#!/usr/bin/env python3
"""Colab gate for the literal source-flow source-localization owner bound."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "60537615aab13f687253473f988bf5e2a7281c4f"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "9c37609b8cdc2a6172c23fb087e76c8fc7ffab93/"
    "scripts/colab_source_flow_point_source_owner_bound_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "b05e4c1551dbc0a1799e96b6fd1203703628c76ab7b5faa8d398f021b9bb6865"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_point_source_owner_bound_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_source_owner_bound_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-source-owner-bound-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-source-owner-bound")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-source-owner-bound-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-source-owner-bound-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-source-owner-bound-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBound.lean":
        "79593551380c35c9b023d2ca04303ed758edf286e4c1ac56ac453ab768174da0",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBoundAudit.lean":
        "3d19746d80d46aa84406b1c139cdcbf7c2e038c9fda06d46e9284f82b263e5dd",
}
runner.QUEUE = [
    (
        "source_flow_source_owner_bound_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBound",
        ],
        None,
    ),
    (
        "source_flow_source_owner_bound_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBoundAudit.lean",
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
