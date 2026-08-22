#!/usr/bin/env python3
"""Colab gate for the Poincare-generated full-complex depth-decay no-go."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "bf1b535367279dbc5df8487a1a56e48dccf76eb6"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "3f39344e2a2e7a8ccd8e12114f7c42db6c3c142a/"
    "scripts/colab_regional_prefix_right_adjoint_owner_decay_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "2fdb08f71e1704cb15b5cc9345a9c79f74c30495ed89f9e59249917f98e204ff"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_right_adjoint_owner_decay_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "full_complex_a_depth_decay_nogo_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "full-complex-a-depth-decay-nogo-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-full-complex-a-depth-decay-nogo")
runner.EVIDENCE = Path(
    "/content/hrpoly-full-complex-a-depth-decay-nogo-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-full-complex-a-depth-decay-nogo-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-full-complex-a-depth-decay-nogo-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFullComplexADepthDecayNoGo.lean":
        "5b30109211b58b21ec66ac0b72af371f365696c895324a165c88f9d8faa4f31e",
    "YangMills/RG/BalabanCMP99SourceGeneratedFullComplexADepthDecayNoGoAudit.lean":
        "d09b106357280a09062b2eac0aebf4737d7cb5269e68c7e974eec1d683810586",
}
runner.QUEUE = [
    (
        "full_complex_a_depth_decay_nogo_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceGeneratedFullComplexADepthDecayNoGo",
        ],
        None,
    ),
    (
        "full_complex_a_depth_decay_nogo_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceGeneratedFullComplexADepthDecayNoGoAudit.lean",
        ],
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
    try:
        from google.colab import files, runtime

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
        print("RUNTIME_UNASSIGN_REQUESTED=1", flush=True)
        runtime.unassign()
    except ImportError:
        pass
    raise SystemExit(code)
