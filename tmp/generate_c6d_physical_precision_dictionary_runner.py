#!/usr/bin/env python3
"""Generate the cold Colab runner for the C6d physical precision dictionary."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_source_separated_ambient_green_validation_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_physical_precision_dictionary_validation.py"
BRICKS = (
    (
        "FinitePiLpTypedKernelReindexRectangularAlgebra",
        (
            "finitePiLpTypedKernelReindex_rect_comp",
            "finitePiLpTypedKernelReindex_adjoint",
            "finitePiLpTypedKernelReindex_adjoint_comp_self",
        ),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground",
        (
            "cmp99Eq360C6dSourceSeparatedPhysicalBackground",
            "cmp99Eq360C6dSourceSeparatedPhysicalBackground_apply",
            "cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv_shift",
        ),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionary",
        (
            "cmp99Eq360C6dSourceSeparatedPhysicalBondEquiv",
            "cmp99Eq360C6dSourceSeparatedCovariantD0_reindex_eq",
            "cmp99Eq360C6dSourceSeparatedCovariantLaplacian_reindex_eq",
        ),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionary",
        (
            "cmp99Eq360C6dSourceSeparatedDirichletPrecision_eq_reindexed_sourceGaugePrecision",
        ),
    ),
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_physical_dictionary_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_PHYSICAL_DICTIONARY_RUNNER_BASE_IMPORT_FAILED")
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
            "Fresh Colab gate for the C6d physical precision dictionary.",
        ),
        (
            "This runner validates the positive- and zero-depth source/audit pairs, all\n"
            "twenty-five public axiom readouts and every repository consumer through\n"
            "``YangMillsCore``.  Passing\n"
            "does not attain window 15, move ``20/41`` or inhabit ``TermSource``.",
            "This runner validates rectangular kernel reindexing, the exact Step-7b\n"
            "physical background, the covariant D0/Laplacian transport and the literal\n"
            "source-gauge precision equality. It checks ten public axiom readouts and\n"
            "every repository consumer through ``YangMillsCore``. Passing closes only\n"
            "the named C6d physical precision dictionary: it does not prove Green\n"
            "decay, the four actions, uniform B0/delta0, window 15, ``20/41`` or\n"
            "``TermSource``.",
        ),
        (
            "c6d-source-separated-ambient-green-v3",
            "c6d-physical-precision-dictionary-v1",
        ),
        (
            "hrpoly-c6d-source-separated-ambient-green",
            "hrpoly-c6d-physical-precision-dictionary",
        ),
        (
            "03_c6d_source_green_yang_mills_core_root",
            "05_c6d_physical_precision_dictionary_yang_mills_core_root",
        ),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_PHYSICAL_DICTIONARY_RUNNER_REPLACEMENT_MISSING")
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
        "C6D_PHYSICAL_DICTIONARY_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=9 stages=9 axiom_blocks=10 "
        "root=YangMillsCore "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
