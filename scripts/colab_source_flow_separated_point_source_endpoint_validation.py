#!/usr/bin/env python3
"""Colab gate for the source-flow separated point-source endpoint."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "ac04749f4cecc3558bb4c985de5ad313c9526c93"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "05fb0c018d7f73b4b8135fc92ae8b2b569abe67f/"
    "scripts/colab_source_flow_separated_endpoint_integrand_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "6d8ab5a7d59c981d11cce56f6fe9df430d20982f1767a3cb637427baeb75f3f7"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_separated_endpoint_integrand_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_separated_point_source_endpoint_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-separated-point-source-endpoint-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-separated-point-source-endpoint")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-separated-point-source-endpoint-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-separated-point-source-endpoint-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-separated-point-source-endpoint-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceEndpoint.lean":
        "3bcb5e592b9d6537e3a215bdb2f05c3c68d179b6721916f377b1b48b49f06727",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceEndpointAudit.lean":
        "999b9b2856371427714cf8cd17a0ea1e8043d270de312a98e3779a9e18997f61",
}
runner.QUEUE = [
    (
        "source_flow_separated_point_source_endpoint_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceEndpoint",
        ],
        None,
    ),
    (
        "source_flow_separated_point_source_endpoint_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceEndpointAudit.lean",
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
