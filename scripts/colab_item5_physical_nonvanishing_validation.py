#!/usr/bin/env python3
"""Colab diagnostic gate for the first three Step-7b item-5 bricks.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, pin gates, robust axiom parser,
evidence archive, and runtime auto-release from the three-species runner.
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

runner.RUNNER_REV = "item5-physical-nonvanishing-v1"
runner.SOURCE_SHA = "baa351bdb57e0824ca127140ad3c1d6d505c8d9a"
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
        "fd08df237493137f4e1e738f7dbdbddfb4eb3c644c3cc73358f2dbf5d0a544b2",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCenteredCoarseMomentumAudit.lean":
        "2fff838c21cfde90a5e27c3388d71e72e0972d60cf428288f81fd81a6f5a664b",
    "YangMills/RG/BalabanCMP89MassZeroCentralFineSymbolNonvanishing.lean":
        "ba5881609bb6f33fa2a2ec3938b822e4231abba9463a8ab69c2a927ef8817456",
    "YangMills/RG/BalabanCMP89MassZeroCentralFineSymbolNonvanishingAudit.lean":
        "820fb51e725810aeefe14d2a9b7fec9e6a98287d9a2bcb8114ad89e9ef23898a",
}

runner.QUEUE = [
    (
        "generated_full_complex_a_positive_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceGeneratedFullComplexAPositive"],
        None,
    ),
    (
        "generated_full_complex_a_positive_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceGeneratedFullComplexAPositiveAudit.lean"],
        4,
    ),
    (
        "centered_coarse_momentum_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatQprimeCenteredCoarseMomentum"],
        None,
    ),
    (
        "centered_coarse_momentum_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatQprimeCenteredCoarseMomentumAudit.lean"],
        4,
    ),
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
    raise SystemExit(runner.main())
