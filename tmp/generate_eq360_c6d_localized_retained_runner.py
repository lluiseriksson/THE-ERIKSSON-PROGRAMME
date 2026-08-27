#!/usr/bin/env python3
"""Generate the pinned cold runner for the source-facing C6d Eq. (3.60)."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_next_real_slice_runner.py"
OUTPUT = ROOT / "scripts" / "colab_eq360_c6d_localized_retained_validation.py"
MODULES = (("BalabanCMP99Eq360C6dLocalizedRetainedPrecision", 19),)


def load_base():
    spec = importlib.util.spec_from_file_location("eq360_c6d_runner_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("EQ360_C6D_RUNNER_BASE_IMPORT_FAILED")
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
            "Cold Colab validation for the source-facing C6d Eq. (3.60) wrapper.",
        ),
        (
            "The queue compiles three promoted PRE-VALIDATION source/audit pairs in\n"
            "dependency order, checks ten public declarations, builds YangMillsCore\n"
            "from the same fresh checkout, and stops at the first real error.  It does not\n"
            "move 20/41 or instantiate TermSource.",
            "The queue compiles the promoted source-facing C6d Eq. (3.60) source/audit\n"
            "pair, checks nineteen public declarations, builds YangMillsCore from the\n"
            "same fresh checkout, and stops at the first real error.  It does not prove\n"
            "the local estimates (3.61)--(3.63), attain window 15, move 20/41, or\n"
            "instantiate TermSource.",
        ),
        ("C6D_NEXT_REAL_SLICE", "EQ360_C6D_LOCALIZED_RETAINED"),
        ("c6d_next_real_slice", "eq360_c6d_localized_retained"),
        ("hrpoly-c6d-next-real-slice", "hrpoly-eq360-c6d-localized-retained"),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("EQ360_C6D_RUNNER_REPLACEMENT_MISSING=" + old[:60])
        content = content.replace(old, new)

    old_dependencies = '''            "YangMills.RG.BalabanCMP99ComplexPhysicalRegionalTower",
            "YangMills.RG.BalabanCMP99ComplexUbarSpecialLinear",
            "YangMills.RG.BalabanCMP99SourceRegionalScale",
            "YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction",
            "YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
            "YangMills.RG.BalabanCMP99SourceRetainedFineExtension",
            "YangMills.RG.BalabanCMP99Eq359TowerRealSliceAgreement",
            "YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime",'''
    new_dependencies = '''            "YangMills.RG.BalabanCMP99SourcePhysicalRealSliceTowerPair",
            "YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusToPhysicalRadiusBudget",
            "YangMills.RG.BalabanCMP99Eq360ComplexRegionalLaplacian",
            "YangMills.RG.BalabanCMP99Eq360ComplexLocalLaplacianPerturbation",
            "YangMills.RG.BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation",
            "YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision",
            "YangMills.RG.BalabanCMP99Eq337PhysicalComplexBaselineRealSlice",'''
    if old_dependencies not in content:
        raise RuntimeError("EQ360_C6D_RUNNER_DEPENDENCY_BLOCK_MISSING")
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
        "EQ360_C6D_RUNNER_GENERATED "
        f"source_sha={args.source_sha} runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
