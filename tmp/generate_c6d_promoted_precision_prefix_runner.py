#!/usr/bin/env python3
"""Generate the pinned cold runner for the promoted C6d precision prefix."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_next_real_slice_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_promoted_precision_prefix_validation.py"
MODULES = (
    ("BalabanCMP99SourcePhysicalRealSliceTowerPair", 5),
    ("BalabanCMP99Eq337ComplexClosedRadiusToPhysicalRadiusBudget", 4),
    ("BalabanCMP99Eq360ComplexRegionalLaplacian", 8),
    ("BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice", 3),
    ("BalabanCMP99Eq360ComplexLocalLaplacianPerturbation", 4),
    ("BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation", 3),
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_promoted_prefix_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_PROMOTED_PREFIX_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def render(source_sha: str, runner_rev: str) -> str:
    base = load_base()
    base.MODULES = MODULES
    content = base.render(source_sha, runner_rev)
    replacements = (
        (
            "Cold Colab validation for the next finite C6d compact real-slice gate.",
            "Cold Colab validation for the promoted C6d precision prefix.",
        ),
        (
            "The queue compiles three promoted PRE-VALIDATION source/audit pairs in\n"
            "dependency order, checks ten public declarations, builds YangMillsCore\n"
            "from the same fresh checkout, and stops at the first real error.  It does not\n"
            "move 20/41 or instantiate TermSource.",
            "The queue compiles six promoted PRE-VALIDATION source/audit pairs in\n"
            "dependency order, checks twenty-seven public declarations, builds\n"
            "YangMillsCore from the same fresh checkout, and stops at the first real\n"
            "error.  It does not attain window 15, move 20/41, or instantiate\n"
            "TermSource.",
        ),
        ("C6D_NEXT_REAL_SLICE", "C6D_PROMOTED_PRECISION_PREFIX"),
        ("c6d_next_real_slice", "c6d_promoted_precision_prefix"),
        ("hrpoly-c6d-next-real-slice", "hrpoly-c6d-promoted-precision-prefix"),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_PROMOTED_PREFIX_REPLACEMENT_MISSING=" + old[:60])
        content = content.replace(old, new)

    old_dependencies = '''            "YangMills.RG.BalabanCMP99ComplexPhysicalRegionalTower",
            "YangMills.RG.BalabanCMP99ComplexUbarSpecialLinear",
            "YangMills.RG.BalabanCMP99SourceRegionalScale",
            "YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction",
            "YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
            "YangMills.RG.BalabanCMP99SourceRetainedFineExtension",
            "YangMills.RG.BalabanCMP99Eq359TowerRealSliceAgreement",
            "YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime",'''
    new_dependencies = '''            "YangMills.RG.BalabanCMP99SourcePhysicalRealSliceTower",
            "YangMills.RG.BalabanCMP99Eq359ComplexRegionalTowerPair",
            "YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusPhysicalBridge",
            "YangMills.RG.BalabanCMP99SourceUbarRadiusBudget",
            "YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointAction",
            "YangMills.RG.PhysicalGaugeOperator",
            "YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
            "YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction",
            "YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport",'''
    if old_dependencies not in content:
        raise RuntimeError("C6D_PROMOTED_PREFIX_DEPENDENCY_BLOCK_MISSING")
    return content.replace(old_dependencies, new_dependencies)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    base = load_base()
    base.require_commit(args.source_sha, "SOURCE")
    content = render(args.source_sha, args.runner_rev)
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "C6D_PROMOTED_PREFIX_RUNNER_GENERATED "
        f"source_sha={args.source_sha} runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
