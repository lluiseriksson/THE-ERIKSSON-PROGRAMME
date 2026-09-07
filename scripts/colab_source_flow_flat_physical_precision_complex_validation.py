#!/usr/bin/env python3
"""Colab gate for the literal source-flow flat complex precision."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "867325d51c978816a58436fcd11675f2a17eea30"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "1dfb352d47683365ec605e914a794b091276c4a4/"
    "scripts/colab_source_flow_flat_qprime_mass_complex_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "9cba00a64ee1f0248a00d05bd7deadda3045da704701d966bf357cc8bf8844c5"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_flat_qprime_mass_complex_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_flat_physical_precision_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-flat-physical-precision-complex-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-flat-physical-precision-complex")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-flat-physical-precision-complex-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-flat-physical-precision-complex-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-flat-physical-precision-complex-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlowFlatPhysicalPrecisionComplexDictionary.lean":
        "6d261d3083dd99cea9fc9fc9ca5c146b825d540f70f4f4dfa1762dd65c0a5113",
    "YangMills/RG/BalabanCMP99SourceFlowFlatPhysicalPrecisionComplexDictionaryAudit.lean":
        "84d5ba1ed00b82ac1e97f0f7922e900bb0262f48fb228c75fa7de255a7f78b91",
}
runner.QUEUE = [
    (
        "source_flow_flat_physical_precision_complex_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceFlowFlatPhysicalPrecisionComplexDictionary",
        ],
        None,
    ),
    (
        "source_flow_flat_physical_precision_complex_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceFlowFlatPhysicalPrecisionComplexDictionaryAudit.lean",
        ],
        1,
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
        from google.colab import runtime

        runtime.unassign()
    except Exception as exc:
        print(
            "RUNTIME_UNASSIGN_STATUS=FAILED "
            + type(exc).__name__ + ": " + str(exc),
            flush=True,
        )
    raise SystemExit(code)
