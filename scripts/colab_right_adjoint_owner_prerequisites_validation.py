#!/usr/bin/env python3
"""Instrumental Colab gate for independent C6c.4d7 owner prerequisites."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "0fe0b1e4720d0d66112c5220ad2717808d49b760"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "26078282adad34a477ad7ab79649d49a14558b41/"
    "scripts/colab_regional_prefix_green_block_owner_decay_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "1e239ab30d12aca72d4c3b89623fd177fcd0a2e3001d57d9d391f41fcf7faa8e"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_green_block_owner_decay_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "right_adjoint_owner_prerequisites_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "right-adjoint-owner-prerequisites-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-right-adjoint-owner-prerequisites")
runner.EVIDENCE = Path(
    "/content/hrpoly-right-adjoint-owner-prerequisites-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-right-adjoint-owner-prerequisites-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-right-adjoint-owner-prerequisites-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99ActiveRegionSourceCovariantAdjointStencil.lean":
        "8155816c7027aac8b719456d35cde14cc17a8ab3df35e9292acd0eb525d87d6e",
    "YangMills/RG/BalabanCMP99ActiveRegionSourceCovariantAdjointStencilAudit.lean":
        "d396e4e358ea0bc51acb7500ab6fd4a8703d71876b1188830c78f6562562dd65",
    "YangMills/RG/FinitePiLpBlockLocalizedSupOwnerKernelComposition.lean":
        "17bae6cd6703a4c24509337f009e0f4cfd7ca12b8d30147679f9208826a99c4c",
    "YangMills/RG/FinitePiLpBlockLocalizedSupOwnerKernelCompositionAudit.lean":
        "78995aac2802c769c3a82b77bc06eb79380423e27694b3be6140b036a7467efe",
}
runner.QUEUE = [
    (
        "right_adjoint_stencil_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99ActiveRegionSourceCovariantAdjointStencil",
        ],
        None,
    ),
    (
        "right_adjoint_stencil_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99ActiveRegionSourceCovariantAdjointStencilAudit.lean",
        ],
        3,
    ),
    (
        "owner_kernel_composition_focal",
        [
            "lake", "build",
            "YangMills.RG.FinitePiLpBlockLocalizedSupOwnerKernelComposition",
        ],
        None,
    ),
    (
        "owner_kernel_composition_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/FinitePiLpBlockLocalizedSupOwnerKernelCompositionAudit.lean",
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
    try:
        from google.colab import files

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(code)
