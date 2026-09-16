#!/usr/bin/env python3
"""Generate one cold runner for C6d D2 and owner-distance rescaling."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_source_separated_ambient_green_validation_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_exact_green_decay_owner_rescaling_validation.py"

POSITIVE_MODULE = "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecay"
POSITIVE_DECLARATIONS = (
    "cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude",
    "cmp99Eq360C6dSourceAmbientBaselinePrecision_exponentialKernelBound",
    "cmp99Eq360C6dSourceSeparatedAmbientPrecision_exponentialKernelBound",
    "cmp99Eq360C6dSourceSeparatedAmbientGreen_exponentialKernelBound",
)
ZERO_MODULE = "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayZeroDepth"
ZERO_DECLARATIONS = (
    "cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero",
    "cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero_exponentialKernelBound",
    "cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_exponentialKernelBound",
)
OWNER_MODULE = "BalabanCMP99Eq360C6dSourceSeparatedOwnerDecayRescaling"
OWNER_DECLARATIONS = (
    "cmp99Eq360C6dSourceSeparated_exponentialKernelBound_rescaleOwner",
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_d2_owner_runner_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_D2_OWNER_RUNNER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def generate(source_sha: str) -> str:
    base = load_base()
    base.BRICKS = (
        (POSITIVE_MODULE, POSITIVE_DECLARATIONS),
        (ZERO_MODULE, ZERO_DECLARATIONS),
        (OWNER_MODULE, OWNER_DECLARATIONS),
    )
    content = base.generate(source_sha)
    replacements = (
        (
            "Fresh Colab gate for both source-carrier C6d ambient Green branches.",
            "Fresh Colab gate for C6d D2 and owner-distance rescaling.",
        ),
        (
            "This runner validates the positive- and zero-depth source/audit pairs, all\n"
            "twenty-five public axiom readouts and every repository consumer through\n"
            "``YangMillsCore``.  Passing\n"
            "does not attain window 15, move ``20/41`` or inhabit ``TermSource``.",
            "This runner validates the positive- and zero-depth exact Green-decay\n"
            "pairs plus exact owner-distance rescaling, all eight public axiom\n"
            "readouts and every repository consumer through one ``YangMillsCore``\n"
            "root. Passing proves only per-depth D2 plus its exact rescaling; it does\n"
            "not prove uniform regional B0/delta0, attain window 15, move ``20/41``\n"
            "or inhabit ``TermSource``.",
        ),
        ("c6d-source-separated-ambient-green-v3", "c6d-d2-owner-rescaling-v2"),
        (
            "hrpoly-c6d-source-separated-ambient-green",
            "hrpoly-c6d-d2-owner-rescaling",
        ),
        (
            "03_c6d_source_green_yang_mills_core_root",
            "04_c6d_d2_owner_rescaling_yang_mills_core_root",
        ),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_D2_OWNER_RUNNER_REPLACEMENT_MISSING")
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
        "C6D_D2_OWNER_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=7 stages=7 axiom_blocks=8 "
        "root=YangMillsCore roots=1 "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
