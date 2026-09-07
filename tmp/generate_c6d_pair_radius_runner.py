#!/usr/bin/env python3
"""Generate the pinned cold runner for the C6d pair/radius bridge gate."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_next_real_slice_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_pair_radius_validation.py"
MODULES = (
    ("BalabanCMP99SourcePhysicalRealSliceTowerPair", 5),
    ("BalabanCMP99Eq337ComplexClosedRadiusToPhysicalRadiusBudget", 4),
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_pair_radius_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_PAIR_RADIUS_RUNNER_BASE_IMPORT_FAILED")
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
            "Cold Colab validation for the C6d terminal pair and radius bridge.",
        ),
        (
            "The queue compiles three promoted PRE-VALIDATION source/audit pairs in\n"
            "dependency order, checks ten public declarations, builds YangMillsCore\n"
            "from the same fresh checkout, and stops at the first real error.  It does not\n"
            "move 20/41 or instantiate TermSource.",
            "The queue compiles two promoted PRE-VALIDATION source/audit pairs, checks\n"
            "nine public declarations, builds YangMillsCore from the same fresh checkout,\n"
            "and stops at the first real error.  It does not move 20/41, attain window 15,\n"
            "or instantiate TermSource.",
        ),
        ("C6D_NEXT_REAL_SLICE", "C6D_PAIR_RADIUS"),
        ("c6d_next_real_slice", "c6d_pair_radius"),
        ("hrpoly-c6d-next-real-slice", "hrpoly-c6d-pair-radius"),
    )
    for old, new in replacements:
        content = content.replace(old, new)
    return content


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
        "C6D_PAIR_RADIUS_RUNNER_GENERATED "
        f"source_sha={args.source_sha} runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
