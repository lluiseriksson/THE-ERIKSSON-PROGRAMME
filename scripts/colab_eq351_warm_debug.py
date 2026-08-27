#!/usr/bin/env python3
"""Warm, non-evidentiary debug queue for the source-facing Eq. (3.51) chain.

This runner deliberately reuses an existing Colab `.lake` graph.  It is only
for finding the first elaboration error before a later cold seal.  It neither
packages evidence nor removes PRE-VALIDATION markers.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import time


QUEUE = (
    (
        "adjoint_composition_source",
        "YangMills/RG/BalabanCMP99ComplexSpecialLinearAdjointComposition.lean",
        ".lake/build/lib/lean/YangMills/RG/"
        "BalabanCMP99ComplexSpecialLinearAdjointComposition.olean",
    ),
    (
        "adjoint_composition_audit",
        "YangMills/RG/BalabanCMP99ComplexSpecialLinearAdjointCompositionAudit.lean",
        ".lake/build/lib/lean/YangMills/RG/"
        "BalabanCMP99ComplexSpecialLinearAdjointCompositionAudit.olean",
    ),
    (
        "positive_factorization_source",
        "YangMills/RG/BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization.lean",
        ".lake/build/lib/lean/YangMills/RG/"
        "BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization.olean",
    ),
    (
        "positive_factorization_audit",
        "YangMills/RG/BalabanCMP99Eq351PhysicalComplexPositiveBondFactorizationAudit.lean",
        ".lake/build/lib/lean/YangMills/RG/"
        "BalabanCMP99Eq351PhysicalComplexPositiveBondFactorizationAudit.olean",
    ),
    (
        "eq360_regional_laplacian_source",
        "tmp/BalabanCMP99Eq360ComplexRegionalLaplacian.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq360ComplexRegionalLaplacian.draft.olean",
    ),
    (
        "eq360_regional_laplacian_audit",
        "tmp/BalabanCMP99Eq360ComplexRegionalLaplacianAudit.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq360ComplexRegionalLaplacianAudit.draft.olean",
    ),
    (
        "eq360_regional_laplacian_real_slice_source",
        "tmp/BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice.draft.olean",
    ),
    (
        "eq360_regional_laplacian_real_slice_audit",
        "tmp/BalabanCMP99Eq360ComplexRegionalLaplacianRealSliceAudit.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq360ComplexRegionalLaplacianRealSliceAudit.draft.olean",
    ),
    (
        "negative_factorization_source",
        "tmp/BalabanCMP99Eq351PhysicalComplexNegativeBondFactorization.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351PhysicalComplexNegativeBondFactorization.draft.olean",
    ),
    (
        "negative_factorization_audit",
        "tmp/BalabanCMP99Eq351PhysicalComplexNegativeBondFactorizationAudit.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351PhysicalComplexNegativeBondFactorizationAudit.draft.olean",
    ),
    (
        "positive_adjoint_source",
        "tmp/BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion.draft.olean",
    ),
    (
        "positive_adjoint_audit",
        "tmp/BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansionAudit.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansionAudit.draft.olean",
    ),
    (
        "oriented_adjoint_source",
        "tmp/BalabanCMP99Eq351PhysicalComplexOrientedAdjointExpansion.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351PhysicalComplexOrientedAdjointExpansion.draft.olean",
    ),
    (
        "oriented_adjoint_audit",
        "tmp/BalabanCMP99Eq351PhysicalComplexOrientedAdjointExpansionAudit.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351PhysicalComplexOrientedAdjointExpansionAudit.draft.olean",
    ),
    (
        "oriented_stencil_source",
        "tmp/BalabanCMP99Eq351ComplexRegionalLaplacianStencil.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351ComplexRegionalLaplacianStencil.draft.olean",
    ),
    (
        "oriented_stencil_audit",
        "tmp/BalabanCMP99Eq351ComplexRegionalLaplacianStencilAudit.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351ComplexRegionalLaplacianStencilAudit.draft.olean",
    ),
    (
        "raw_regrouping_source",
        "tmp/BalabanCMP99Eq351ComplexLaplacianRegroupingRaw.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351ComplexLaplacianRegroupingRaw.draft.olean",
    ),
    (
        "raw_regrouping_audit",
        "tmp/BalabanCMP99Eq351ComplexLaplacianRegroupingRawAudit.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351ComplexLaplacianRegroupingRawAudit.draft.olean",
    ),
)


def run(repo: Path, stage: str, source: str, output: str) -> int:
    output_path = repo / output
    output_path.parent.mkdir(parents=True, exist_ok=True)
    command = ["lake", "env", "lean", source, "-o", output]
    print(f"STAGE={stage} CMD={command!r}", flush=True)
    start = time.perf_counter()
    child = subprocess.run(command, cwd=repo, check=False)
    elapsed = time.perf_counter() - start
    print(
        f"STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
    return child.returncode


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    if re.fullmatch(r"[0-9a-f]{40}", args.source_sha) is None:
        raise RuntimeError("EQ351_WARM_SOURCE_SHA_INVALID")
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repo, check=True,
        capture_output=True, text=True, encoding="utf-8"
    ).stdout.strip()
    if head != args.source_sha:
        raise RuntimeError(
            f"EQ351_WARM_SOURCE_SHA_MISMATCH={head} WANT={args.source_sha}"
        )
    print(
        f"EQ351_WARM_DEBUG_BEGIN source_sha={args.source_sha} stages={len(QUEUE)}",
        flush=True,
    )
    for stage, source, output in QUEUE:
        code = run(repo, stage, source, output)
        if code != 0:
            print(f"EQ351_WARM_DEBUG_FINAL_STATUS=FAIL FIRST_ERROR={stage}", flush=True)
            return code
    print("EQ351_WARM_DEBUG_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
