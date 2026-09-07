#!/usr/bin/env python3
"""Generate the cold Colab runner for C6d owner-distance rescaling."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_finite_pilp_distance_rescaling_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_owner_decay_rescaling_validation.py"
MODULE = "BalabanCMP99Eq360C6dSourceSeparatedOwnerDecayRescaling"
DECLARATIONS = (
    "cmp99Eq360C6dSourceSeparated_exponentialKernelBound_rescaleOwner",
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_owner_rescaling_runner_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_OWNER_RESCALING_RUNNER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def generate(source_sha: str) -> str:
    base = load_base()
    base.MODULE = MODULE
    base.DECLARATIONS = DECLARATIONS
    content = base.generate(source_sha)
    replacements = (
        (
            "Fresh Colab gate for exact rectangular kernel-distance rescaling.",
            "Fresh Colab gate for exact C6d owner-distance rescaling.",
        ),
        (
            "This runner validates one algebraic distance-rescaling theorem, its\n"
            "single public axiom readout and every repository consumer through\n"
            "``YangMillsCore``. Passing does not construct D2, any physical action,\n"
            "uniform B0/delta0, window 15, move ``20/41`` or inhabit ``TermSource``.",
            "This runner validates the exact C6d specialization of the algebraic\n"
            "distance-rescaling theorem, its single public axiom readout and every\n"
            "repository consumer through ``YangMillsCore``. Passing does not construct\n"
            "D2, any physical action, uniform B0/delta0, window 15, move ``20/41``\n"
            "or inhabit ``TermSource``.",
        ),
        (
            "finite-pilp-distance-rescaling-v1",
            "c6d-owner-decay-rescaling-v1",
        ),
        (
            "hrpoly-finite-pilp-distance-rescaling",
            "hrpoly-c6d-owner-decay-rescaling",
        ),
        (
            "02_finite_pilp_distance_rescaling_yang_mills_core_root",
            "02_c6d_owner_decay_rescaling_yang_mills_core_root",
        ),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_OWNER_RESCALING_RUNNER_REPLACEMENT_MISSING")
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
        "C6D_OWNER_RESCALING_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=3 stages=3 axiom_blocks=1 "
        "root=YangMillsCore "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
