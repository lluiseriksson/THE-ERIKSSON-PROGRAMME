#!/usr/bin/env python3
"""Colab gate for the source-flow separated Green Fourier endpoint."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "d8309600d4898a5d8ec35bada6130acb1091fd56"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "5d7034ce630f04d860529b7c40915e87f32835a2/"
    "scripts/colab_source_flow_flat_physical_precision_complex_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "3efdc2b2f80cd8851905e61c7ea47bd3ee3ab97e85dd7aa255c17b8f83ffd8c4"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_flat_physical_precision_complex_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_separated_green_fourier_endpoint_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-separated-green-fourier-endpoint-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-separated-green-fourier-endpoint")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-separated-green-fourier-endpoint-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-separated-green-fourier-endpoint-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-separated-green-fourier-endpoint-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenFourierEndpoint.lean":
        "6524f6b373d4ec8e8aeba691086001693f49c2efe894b8723329f420758653a2",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenFourierEndpointAudit.lean":
        "5ffe59d4ada76e17981476ba548a208ae9e05feca02080a326530016e76e6d1b",
}
runner.QUEUE = [
    (
        "source_flow_separated_green_fourier_endpoint_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenFourierEndpoint",
        ],
        None,
    ),
    (
        "source_flow_separated_green_fourier_endpoint_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenFourierEndpointAudit.lean",
        ],
        4,
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
