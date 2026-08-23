#!/usr/bin/env python3
"""Colab gate for the source-flow uniform complex window and amplitude."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "a0727792b0ae8235e13d6f26a874858c63474a1c"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "d72089f11838c8a720c11a4b77054a73a520419f/"
    "scripts/colab_full_complex_a_depth_decay_nogo_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "57b518f116f315c25c383d235a46aeec9ac4bee1832b268bc5bd09f70e7a9f65"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_full_complex_a_depth_decay_nogo_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "source_mass_uniform_complex_window_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-mass-uniform-complex-window-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-mass-uniform-complex-window")
runner.EVIDENCE = Path(
    "/content/hrpoly-source-mass-uniform-complex-window-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-source-mass-uniform-complex-window-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-source-mass-uniform-complex-window-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP85SourceMassParameterUniformComplexWindow.lean":
        "9e53c37555cb9b469355ba41470c8b6be359ff4fd6f0b12bc8b816d8330562d1",
    "YangMills/RG/BalabanCMP85SourceMassParameterUniformComplexWindowAudit.lean":
        "df269b65b8b94bcf29e27b722675c00886f4704c790316f22a4dd6f643e03247",
}
runner.QUEUE = [
    (
        "source_mass_uniform_complex_window_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP85SourceMassParameterUniformComplexWindow",
        ],
        None,
    ),
    (
        "source_mass_uniform_complex_window_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP85SourceMassParameterUniformComplexWindowAudit.lean",
        ],
        7,
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
