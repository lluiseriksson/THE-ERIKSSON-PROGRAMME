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
        "covariant_divergence_source",
        "tmp/BalabanCMP99Eq351PhysicalComplexCovariantDivergence.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351PhysicalComplexCovariantDivergence.draft.olean",
    ),
    (
        "covariant_divergence_audit",
        "tmp/BalabanCMP99Eq351PhysicalComplexCovariantDivergenceAudit.draft.lean",
        ".lake/build/lib/lean/tmp/"
        "BalabanCMP99Eq351PhysicalComplexCovariantDivergenceAudit.draft.olean",
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


TMP_IMPORT = re.compile(r"(?m)^import\s+(tmp\.[A-Za-z0-9_.]+)\s*$")
FORBIDDEN = re.compile(r"\b(?:sorry|admit)\b")


def source_module(source: str) -> str:
    if not source.endswith(".lean"):
        raise RuntimeError(f"EQ351_WARM_SOURCE_SUFFIX_INVALID={source}")
    return source[:-5].replace("/", ".").replace("\\", ".")


def preflight(repo: Path) -> None:
    sources = [source for _stage, source, _output in QUEUE]
    outputs = [output for _stage, _source, output in QUEUE]
    if len(sources) != len(set(sources)):
        raise RuntimeError("EQ351_WARM_SOURCE_DUPLICATE")
    if len(outputs) != len(set(outputs)):
        raise RuntimeError("EQ351_WARM_OUTPUT_DUPLICATE")

    positions = {source_module(source): index for index, source in enumerate(sources)}
    for index, source in enumerate(sources):
        path = repo / source
        if not path.is_file():
            raise RuntimeError(f"EQ351_WARM_SOURCE_MISSING={source}")
        text = path.read_text(encoding="utf-8-sig")
        if source.startswith("tmp/"):
            marker_count = text.count("PRE-VALIDATION:")
            if marker_count != 1:
                raise RuntimeError(
                    f"EQ351_WARM_PREVALIDATION_COUNT={source}:{marker_count} WANT=1"
                )
            forbidden = FORBIDDEN.search(text)
            if forbidden is not None:
                raise RuntimeError(
                    f"EQ351_WARM_FORBIDDEN_TOKEN={source}:{forbidden.group(0)}"
                )
        for imported in TMP_IMPORT.findall(text):
            dependency = positions.get(imported)
            if dependency is None:
                raise RuntimeError(
                    f"EQ351_WARM_TMP_IMPORT_OUTSIDE_QUEUE={source}:{imported}"
                )
            if dependency >= index:
                raise RuntimeError(
                    f"EQ351_WARM_TMP_IMPORT_ORDER={source}:{imported}:"
                    f"dependency={dependency}:consumer={index}"
                )
    print(
        f"EQ351_WARM_PREFLIGHT_OK stages={len(QUEUE)} "
        f"drafts={sum(source.startswith('tmp/') for source in sources)}",
        flush=True,
    )


def cache_base_preflight(repo: Path, base_sha: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", base_sha) is None:
        raise RuntimeError("EQ351_WARM_CACHE_BASE_SHA_INVALID")
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", base_sha, "HEAD"],
        cwd=repo,
        check=False,
    )
    if ancestor.returncode != 0:
        raise RuntimeError(f"EQ351_WARM_CACHE_BASE_NOT_ANCESTOR={base_sha}")
    changed = subprocess.run(
        ["git", "diff", "--name-only", f"{base_sha}..HEAD", "--", "YangMills"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    ).stdout.splitlines()
    changed_lean = sorted(path for path in changed if path.endswith(".lean"))
    queued = {source for _stage, source, _output in QUEUE}
    outside = [path for path in changed_lean if path not in queued]
    if outside:
        raise RuntimeError(
            "EQ351_WARM_CHANGED_PROJECT_SOURCE_OUTSIDE_QUEUE=" + ",".join(outside)
        )
    print(
        f"EQ351_WARM_CACHE_BASE_OK base_sha={base_sha} "
        f"changed_project_sources={len(changed_lean)}",
        flush=True,
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
    parser.add_argument("--cache-base-sha", required=True)
    parser.add_argument("--preflight-only", action="store_true")
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
    preflight(repo)
    cache_base_preflight(repo, args.cache_base_sha)
    if args.preflight_only:
        print("EQ351_WARM_PREFLIGHT_ONLY_OK", flush=True)
        return 0
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
