#!/usr/bin/env python3
"""Colab gate for the literal source-flow flat Qprime mass dictionary."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request

SOURCE_SHA = "e70b91c9e131e302519a710e4d5f6b4d56a92c2f"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "2105cd888d166c07e63a0f1a973fc3bb03e34994/"
    "scripts/colab_source_flow_flat_precision_scalar_dictionary_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "d5a08ff63276f910dd354c4274d74645d7d2af38f411dd19b5bf995dbfaa4cee"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_source_flow_flat_precision_scalar_dictionary_validation.py"
)

payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_flow_flat_qprime_mass_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-flow-flat-qprime-mass-complex-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-flow-flat-qprime-mass-complex")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-flow-flat-qprime-mass-complex-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-flow-flat-qprime-mass-complex-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-flow-flat-qprime-mass-complex-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlowFlatQprimeMassComplexDictionary.lean":
        "d02c2c94c167a080c09f21d2b4df5e831f9d8db9b20296f50beae8948b6af183",
    "YangMills/RG/BalabanCMP99SourceFlowFlatQprimeMassComplexDictionaryAudit.lean":
        "827c6100e1814ddd48391c96943eb6f52a703c9364eb88053b02e3856192e41c",
}
runner.QUEUE = [
    (
        "source_flow_flat_qprime_mass_complex_focal",
        ["lake", "build",
         "YangMills.RG.BalabanCMP99SourceFlowFlatQprimeMassComplexDictionary"],
        None,
    ),
    (
        "source_flow_flat_qprime_mass_complex_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP99SourceFlowFlatQprimeMassComplexDictionaryAudit.lean"],
        3,
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
        print("EVIDENCE_DOWNLOAD_STATUS=FAILED " + type(exc).__name__ +
              ": " + str(exc), flush=True)
    print("RUNTIME_UNASSIGN_REQUESTED=1", flush=True)
    try:
        from google.colab import runtime
        runtime.unassign()
    except Exception as exc:
        print("RUNTIME_UNASSIGN_STATUS=FAILED " + type(exc).__name__ +
              ": " + str(exc), flush=True)
    raise SystemExit(code)
