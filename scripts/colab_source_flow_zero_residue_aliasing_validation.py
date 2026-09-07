#!/usr/bin/env python3
"""Colab gate for source-flow zero-residue aliasing."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "71c0d7e746e41b67d692d6a4c3da0ff41083ba3c"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "b1fb9523c07836a74ace00b4723961fe4f217440/"
    "scripts/colab_source_flow_separated_point_source_endpoint_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "683fff31fa8c38015c4da354eb2d003bbc709eb588bf5439dfebbcec1b4604d8"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_separated_point_source_endpoint_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_zero_residue_aliasing_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-zero-residue-aliasing-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-zero-residue-aliasing")
runner.EVIDENCE = Path("/content/hrpoly-source-flow-zero-residue-aliasing-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-zero-residue-aliasing-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-zero-residue-aliasing-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalZeroResidueAliasing.lean":
        "a7407c719ddd225ce5469ef76c71183ce7c599180dbb2ffce6e29c437e168e1b",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalZeroResidueAliasingAudit.lean":
        "35ddd8676aca295dc111936fc6fb28a600e3333b7df53611db51ead1634aaac0",
}
runner.QUEUE = [
    (
        "source_flow_zero_residue_aliasing_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalZeroResidueAliasing",
        ],
        None,
    ),
    (
        "source_flow_zero_residue_aliasing_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalZeroResidueAliasingAudit.lean",
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
