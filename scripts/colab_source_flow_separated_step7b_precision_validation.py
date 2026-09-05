#!/usr/bin/env python3
"""Colab gate for the source-flow separated Step-7b precision dictionary."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "27c05dc43db1b9f311018dba11ed2847e4010dc4"
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
    "source_flow_separated_step7b_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-separated-step7b-precision-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-separated-step7b-precision")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-separated-step7b-precision-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-separated-step7b-precision-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-separated-step7b-precision-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalStep7bPrecisionDictionary.lean":
        "fe0f52e67a8606d905aac86f96c6de9cfa0f68f958940c2761fab82936f03eb2",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalStep7bPrecisionDictionaryAudit.lean":
        "dd7954fce9edb78c3143bef3afdd6a790b5ddb074e9a54290c83f39bb5f70656",
}
runner.QUEUE = [
    (
        "source_flow_separated_step7b_precision_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalStep7bPrecisionDictionary",
        ],
        None,
    ),
    (
        "source_flow_separated_step7b_precision_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalStep7bPrecisionDictionaryAudit.lean",
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
