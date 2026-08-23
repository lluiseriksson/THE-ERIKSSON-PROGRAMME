#!/usr/bin/env python3
"""Colab gate for the literal source-flow flat ambient inverse pair."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "dd188139a03294d95e6c75bb7a9ef222e2e80d6e"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "60060424d7364af4de8bacee50537d9c7a26b34f/"
    "scripts/colab_source_mass_uniform_complex_window_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "5b88b57d5b57e450f9454f84f565dfabf67511e54a6fd466df0859565f7820d8"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_mass_uniform_complex_window_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_flat_ambient_green_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-flat-ambient-green-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-flat-ambient-green")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-flat-ambient-green-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-flat-ambient-green-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-flat-ambient-green-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreen.lean":
        "69f7162a68cf6115719ef225fb8e153afce677a2d170a5e7e8716de9a33d3a2f",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreenAudit.lean":
        "c4f1e5fe28d8bf30f9a23503c99615f4ab87ca45e31845ff80c1d84c0eb4d0fe",
}
runner.QUEUE = [
    (
        "source_flow_flat_ambient_green_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreen",
        ],
        None,
    ),
    (
        "source_flow_flat_ambient_green_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreenAudit.lean",
        ],
        5,
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
        from google.colab import files, runtime

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
        print("RUNTIME_UNASSIGN_REQUESTED=1", flush=True)
        runtime.unassign()
    except ImportError:
        pass
    raise SystemExit(code)
