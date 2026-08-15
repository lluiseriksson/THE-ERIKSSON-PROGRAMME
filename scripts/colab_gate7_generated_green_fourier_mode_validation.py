#!/usr/bin/env python3
"""Colab diagnostic gate for the generated Green one-mode Fourier fibre.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol.  Its sole queue is the
Gate-7 one-mode Fourier specialization and its four-declaration audit.  It
does not prove a continuous Brillouin integral, a regional Green bound, a
uniform ``B0``, or attainment of window 15.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
SPEC = importlib.util.spec_from_file_location("gate7_fourier_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "gate7-generated-green-fourier-v1"
runner.SOURCE_SHA = "bcc852cee5e709bff91fad7de26fa21cff754e1f"
runner.ROOT = Path("/content/hrpoly-gate7-generated-green-fourier")
runner.EVIDENCE = Path("/content/hrpoly-gate7-generated-green-fourier-evidence")
runner.ARCHIVE = Path("/content/hrpoly-gate7-generated-green-fourier-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-gate7-generated-green-fourier-paths.txt")

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierMode.lean":
        "1ac7f4c87f28c28f653b91a9a7afffa92194d88d1ff5a9d175a3d1842c761aca",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierModeAudit.lean":
        "d2ccb839a72db990c1d014d373b85228f290befee643bb8b1cb37c26f10ea25a",
}

runner.QUEUE = [
    (
        "generated_green_fourier_mode_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierMode",
        ],
        None,
    ),
    (
        "generated_green_fourier_mode_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierModeAudit.lean",
        ],
        4,
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
    raise SystemExit(runner.main())
