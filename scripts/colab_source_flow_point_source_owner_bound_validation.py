#!/usr/bin/env python3
"""Colab gate for the literal source-flow point-source owner bound."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "934efa2a281824db90d13724eb143f7df2a7c4db"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "224684a63e149c6915fa519ba3be6e3a4b464ac5/"
    "scripts/colab_source_flow_point_source_zero_residue_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "acc8e219e4c62bbdcfbad2ad51aa1b34e077f1d5ebc3dd18a8adda090678832f"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_point_source_zero_residue_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_point_source_owner_bound_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-point-source-owner-bound-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-point-source-owner-bound")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-point-source-owner-bound-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-point-source-owner-bound-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-point-source-owner-bound-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceOwnerBound.lean":
        "df69bd46f04d6a4a6b185ce59ea99251f99c085061f6f8da076f97b390d95490",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceOwnerBoundAudit.lean":
        "8e9751454782a53562d671a7f7336f7b5b0021bc1ad4d3956c11ce327d196403",
}
runner.QUEUE = [
    (
        "source_flow_point_source_owner_bound_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceOwnerBound",
        ],
        None,
    ),
    (
        "source_flow_point_source_owner_bound_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceOwnerBoundAudit.lean",
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
