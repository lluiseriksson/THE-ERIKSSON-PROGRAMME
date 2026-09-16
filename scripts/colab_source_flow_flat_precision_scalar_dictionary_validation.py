#!/usr/bin/env python3
"""Colab gate for the literal source-flow flat scalar precision dictionary."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "7344038e2c99fd2ddc679d3a3a4669c0041c9edd"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "c7011317bb7b49887f775304c122d2e76b0a30bc/"
    "scripts/colab_source_flow_flat_ambient_green_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "f430569a2acf95e013e61bd231d5389ea92b0c3c8130cadbfa1e065d42eddd7c"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_flat_ambient_green_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_flat_precision_scalar_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-flat-precision-scalar-v2"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-flat-precision-scalar")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-flat-precision-scalar-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-flat-precision-scalar-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-flat-precision-scalar-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlowFlatPrecisionScalarDictionary.lean":
        "c0efa07994d192d8393557ae47bcafd207ae28cfeb7210c6fb25e8602b3074af",
    "YangMills/RG/BalabanCMP99SourceFlowFlatPrecisionScalarDictionaryAudit.lean":
        "3a12923751851ce4563965e9a35d1573459cc41068ade43910d7643fd08a7cfe",
}
runner.QUEUE = [
    (
        "source_flow_flat_precision_scalar_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceFlowFlatPrecisionScalarDictionary",
        ],
        None,
    ),
    (
        "source_flow_flat_precision_scalar_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceFlowFlatPrecisionScalarDictionaryAudit.lean",
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
