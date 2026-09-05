#!/usr/bin/env python3
"""Generate the cold Colab runner for the remaining C6d action prefix."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_source_separated_ambient_green_validation_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_four_action_prefix_validation.py"
BRICKS = (
    (
        "BalabanCMP99Eq342LeftDerivativeFromValueBound",
        ("cmp99Eq342_leftDerivative_blockLocalizedSupBound_of_value",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivative",
        ("cmp99Eq360C6dSourceSeparatedAmbientGreen_leftDerivative_blockLocalizedSupBound",),
    ),
    (
        "BalabanCMP99Eq342LaplacianFromLeftDerivativeBound",
        ("cmp99Eq342_laplacian_blockLocalizedSupBound_of_leftDerivative",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacian",
        ("cmp99Eq360C6dSourceSeparatedAmbientGreen_laplacian_blockLocalizedSupBound",),
    ),
    (
        "BalabanCMP99Eq342RightAdjointFromValueBound",
        ("cmp99Eq342_rightAdjoint_blockLocalizedSupBound_of_value",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjoint",
        ("cmp99Eq360C6dSourceSeparatedAmbientGreen_rightAdjoint_blockLocalizedSupBound",),
    ),
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_four_action_prefix_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_FOUR_ACTION_PREFIX_RUNNER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def generate(source_sha: str) -> str:
    base = load_base()
    base.BRICKS = BRICKS
    content = base.generate(source_sha)
    replacements = (
        (
            "Fresh Colab gate for both source-carrier C6d ambient Green branches.",
            "Fresh Colab gate for the remaining C6d fixed-depth actions.",
        ),
        (
            "This runner validates the positive- and zero-depth source/audit pairs, all\n"
            "twenty-five public axiom readouts and every repository consumer through\n"
            "``YangMillsCore``.  Passing\n"
            "does not attain window 15, move ``20/41`` or inhabit ``TermSource``.",
            "This runner validates the generic and literal C6d left-derivative,\n"
            "covariant-Laplacian and right-adjoint source/audit pairs, all six public\n"
            "axiom readouts and every repository consumer through ``YangMillsCore``.\n"
            "Passing remains fixed-depth: it does not prove uniform B0/delta0, attain\n"
            "window 15, move ``20/41`` or inhabit ``TermSource``.",
        ),
        (
            "c6d-source-separated-ambient-green-v3",
            "c6d-four-action-prefix-v1",
        ),
        (
            "hrpoly-c6d-source-separated-ambient-green",
            "hrpoly-c6d-four-action-prefix",
        ),
        (
            "03_c6d_source_green_yang_mills_core_root",
            "07_c6d_four_action_prefix_yang_mills_core_root",
        ),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_FOUR_ACTION_PREFIX_RUNNER_REPLACEMENT_MISSING")
        content = content.replace(old, new)
    return content


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    content = generate(args.source_sha)
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "C6D_FOUR_ACTION_PREFIX_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=13 stages=13 axiom_blocks=6 "
        "root=YangMillsCore "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
