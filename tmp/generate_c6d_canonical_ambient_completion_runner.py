#!/usr/bin/env python3
"""Generate the cold Colab runner for canonical ambient completion."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_source_separated_ambient_green_validation_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_canonical_ambient_completion_validation.py"
GENERIC_MODULE = "BalabanCMP99ActiveRegionCanonicalAmbientCompletion"
GENERIC_DECLARATIONS = (
    "cmp99ActiveRegionZeroProjection",
    "cmp99ActiveRegionZeroComplementProjection",
    "norm_sq_cmp99ActiveRegionZeroProjection_add_complement",
    "inner_cmp99ActiveRegionZeroComplementProjection_self",
    "cmp99ActiveRegionCanonicalAmbientCompletion",
    "isCoerciveCLM_cmp99ActiveRegionCanonicalAmbientCompletion",
    "cmp99RegionalDirichletPrecision_canonicalAmbientCompletion_eq",
    "cmp99RegionalDirichletGreen_canonicalAmbientCompletion_eq",
    "cmp99RegionalDirichletGreen_canonicalAmbientCompletion_compressed_eq",
)
INTEGRATION_MODULE = "BalabanCMP99Eq360C6dCanonicalAmbientCompletion"
INTEGRATION_DECLARATIONS = (
    "cmp99Eq360C6dSourceSeparatedCanonicalAmbientCompletion_green_eq",
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_completion_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_CANONICAL_COMPLETION_RUNNER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def generate(source_sha: str) -> str:
    base = load_base()
    base.BRICKS = (
        (GENERIC_MODULE, GENERIC_DECLARATIONS),
        (INTEGRATION_MODULE, INTEGRATION_DECLARATIONS),
    )
    content = base.generate(source_sha)
    replacements = (
        (
            "Fresh Colab gate for both source-carrier C6d ambient Green branches.",
            "Fresh Colab gate for canonical regional ambient completion.",
        ),
        (
            "This runner validates the positive- and zero-depth source/audit pairs, all\n"
            "twenty-five public axiom readouts and every repository consumer through\n"
            "``YangMillsCore``.  Passing\n"
            "does not attain window 15, move ``20/41`` or inhabit ``TermSource``.",
            "This runner validates the generic and C6d integration source/audit\n"
            "pairs, all ten public axiom readouts and every repository consumer\n"
            "through ``YangMillsCore``. Passing closes only the carrier/inverse\n"
            "adapter; it does not prove the four actions, attain window 15, move\n"
            "``20/41`` or inhabit ``TermSource``.\n",
        ),
        (
            "c6d-source-separated-ambient-green-v2",
            "c6d-canonical-ambient-completion-v4",
        ),
        (
            "hrpoly-c6d-source-separated-ambient-green",
            "hrpoly-c6d-canonical-ambient-completion",
        ),
        (
            "03_c6d_source_green_yang_mills_core_root",
            "03_c6d_canonical_ambient_completion_yang_mills_core_root",
        ),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_CANONICAL_COMPLETION_RUNNER_REPLACEMENT_MISSING")
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
        "C6D_CANONICAL_AMBIENT_COMPLETION_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=5 stages=5 axiom_blocks=10 "
        "root=YangMillsCore "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
