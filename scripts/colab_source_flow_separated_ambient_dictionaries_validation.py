#!/usr/bin/env python3
"""Colab gate for source-flow separated ambient dictionaries."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "c4d287594d95ed4dd1ca13713738246480b268f4"
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
    "source_flow_separated_ambient_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-separated-ambient-dictionaries-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-separated-ambient-dictionaries")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-separated-ambient-dictionaries-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-separated-ambient-dictionaries-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-separated-ambient-dictionaries-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreenComplexification.lean":
        "16506cba6c8e9bb4ec5902234d574b164f0b0787512658d2dfc342f83df54fa1",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreenComplexificationAudit.lean":
        "0423710f52749542013e10bc6e8cf9653352b52dee7610a2d2e7fb6e8dee3901",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPrecisionDictionary.lean":
        "362b9fd67e17b0094b9dd74379e43c8e1f0f0387208be22d9afec72d03b543d9",
    "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPrecisionDictionaryAudit.lean":
        "8d39990e1ef73ca4457b14ba09031e427c75dbe468c195d6117459db8562ce19",
}
runner.QUEUE = [
    (
        "source_flow_separated_ambient_complexification_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreenComplexification",
        ],
        None,
    ),
    (
        "source_flow_separated_ambient_complexification_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreenComplexificationAudit.lean",
        ],
        2,
    ),
    (
        "source_flow_separated_physical_precision_dictionary_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPrecisionDictionary",
        ],
        None,
    ),
    (
        "source_flow_separated_physical_precision_dictionary_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPrecisionDictionaryAudit.lean",
        ],
        2,
    ),
]


if __name__ == "__main__":
    real_unassign = None
    try:
        from google.colab import runtime

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
