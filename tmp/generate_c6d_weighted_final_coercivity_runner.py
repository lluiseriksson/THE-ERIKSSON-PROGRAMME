#!/usr/bin/env python3
"""Generate the cold runner for weighted/final C6d plus coercivity."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_weighted_final_prefix_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_weighted_final_coercivity_validation.py"
MODULES = (
    ("BalabanCMP99ActiveRegionCanonicalAmbientCompletion", 8),
    ("BalabanCMP99SourceWeightedGaugePrecisionDictionary", 3),
    ("BalabanCMP99Eq360WeightedPrecisionRealSlice", 1),
    ("BalabanCMP99Eq360C6dLocalizedRetainedPrecision", 30),
    ("BalabanCMP99SourceActiveRegionTerminalCoercivity", 8),
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_wfc_runner_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_WFC_RUNNER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def render(source_sha: str, runner_rev: str) -> str:
    base = load_base()
    base.MODULES = MODULES
    content = base.render(source_sha, runner_rev)
    replacements = (
        ("four promoted PRE-VALIDATION source/audit pairs", "five promoted PRE-VALIDATION source/audit pairs"),
        ("checks forty-two public declarations", "checks fifty public declarations"),
        ("C6D_WEIGHTED_FINAL_PREFIX", "C6D_WEIGHTED_FINAL_COERCIVITY"),
        ("c6d_weighted_final_prefix", "c6d_weighted_final_coercivity"),
        ("hrpoly-c6d-weighted-final-prefix", "hrpoly-c6d-weighted-final-coercivity"),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_WFC_REPLACEMENT_MISSING=" + old)
        content = content.replace(old, new)
    return content


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    base = load_base()
    base.load_base().load_base().require_commit(args.source_sha, "SOURCE")
    content = render(args.source_sha, args.runner_rev)
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "C6D_WEIGHTED_FINAL_COERCIVITY_RUNNER_GENERATED "
        f"source_sha={args.source_sha} runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
