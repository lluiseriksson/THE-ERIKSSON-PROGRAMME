#!/usr/bin/env python3
"""Colab diagnostic resume gate for the third Step-7b item-5 brick.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, pin gates, robust axiom parser,
evidence archive, and runtime auto-release from the three-species runner.
The first two bricks already passed on the exact parent checkpoint; this queue
starts at the only source file changed by the import-boundary repair.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
SPEC = importlib.util.spec_from_file_location("item5_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "item5-mass-zero-central-resume-v3"
runner.SOURCE_SHA = "6ffd5b73974ef9ce8207d58ea1d5f78e37196c3f"
runner.ROOT = Path("/content/hrpoly-item5-physical-nonvanishing")
runner.EVIDENCE = Path("/content/hrpoly-item5-physical-nonvanishing-evidence")
runner.ARCHIVE = Path("/content/hrpoly-item5-physical-nonvanishing-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-item5-physical-nonvanishing-paths.txt")

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFullComplexAPositive.lean":
        "45fa2dffa4945768e2e39b604a05f75da2e8956c69a3d21b5e2daf9d88aefb3f",
    "YangMills/RG/BalabanCMP99SourceGeneratedFullComplexAPositiveAudit.lean":
        "d7a91ea26380631aa5d71702b716208d17d1b295f135559045a502637be16cfc",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCenteredCoarseMomentum.lean":
        "fb77288e77d68a23544490c96212f36c29570394354ea4c1b922f8ecae20ee46",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCenteredCoarseMomentumAudit.lean":
        "2fff838c21cfde90a5e27c3388d71e72e0972d60cf428288f81fd81a6f5a664b",
    "YangMills/RG/BalabanCMP89MassZeroCentralFineSymbolNonvanishing.lean":
        "cb0556e469d6b9f95595411ed84ba10a29a1a2d1adf88c1c6137f40a8c128f05",
    "YangMills/RG/BalabanCMP89MassZeroCentralFineSymbolNonvanishingAudit.lean":
        "820fb51e725810aeefe14d2a9b7fec9e6a98287d9a2bcb8114ad89e9ef23898a",
}

runner.QUEUE = [
    (
        "mass_zero_central_fine_nonvanishing_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89MassZeroCentralFineSymbolNonvanishing"],
        None,
    ),
    (
        "mass_zero_central_fine_nonvanishing_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89MassZeroCentralFineSymbolNonvanishingAudit.lean"],
        3,
    ),
]


if __name__ == "__main__":
    # This runner is launched as a child of the single Colab notebook cell.
    # Releasing the runtime from the child can kill the parent before its
    # captured transcript is flushed, losing both stdout and `/content`
    # evidence.  The parent owns the final release after printing the complete
    # child transcript and archive hash.
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    raise SystemExit(runner.main())
