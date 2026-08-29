#!/usr/bin/env python3
"""Generate the cold Colab runner for the exact post-Green decay prefix."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_source_separated_ambient_green_validation_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_post_green_decay_prefix_validation.py"
DECAY_MODULE = "BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecay"
DECAY_DECLARATIONS = (
    "cmp99SourceActiveRegionFullCompanionPrecisionUpperBound",
    "cmp99SourceActiveRegionFullCompanionPrecisionUpperBound_pos",
    "cmp99SourceActiveRegionFullCompanion_QprimeMass_finiteRange",
    "norm_cmp99SourceActiveRegionFullCompanionPrecision_le",
    "cmp99SourceActiveRegionFullCompanionPrecision_kernelBound",
    "cmp99SourceActiveRegionFullCompanionPrecision_finiteRange",
    "cmp99SourceActiveRegionFullCompanionPrecision_exponentialKernelBound",
)
METRIC_MODULE = "BalabanCMP99Eq360C6dSourceSeparatedAmbientMetric"
METRIC_DECLARATIONS = (
    "finBoxDist_cmp99SourceFullActiveRegionSiteEquiv",
    "finBoxDist_cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv",
    "finBoxDist_cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv",
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_post_green_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_POST_GREEN_RUNNER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def generate(source_sha: str) -> str:
    base = load_base()
    base.BRICKS = (
        (DECAY_MODULE, DECAY_DECLARATIONS),
        (METRIC_MODULE, METRIC_DECLARATIONS),
    )
    content = base.generate(source_sha)
    replacements = (
        (
            "Fresh Colab gate for both source-carrier C6d ambient Green branches.",
            "Fresh Colab gate for the exact post-Green localization prefix.",
        ),
        (
            "This runner validates the positive- and zero-depth source/audit pairs, all\n"
            "twenty-five public axiom readouts and every repository consumer through\n"
            "``YangMillsCore``.  Passing\n"
            "does not attain window 15, move ``20/41`` or inhabit ``TermSource``.",
            "This runner validates the literal full-companion precision localization\n"
            "and all three named metric transports, their ten public axiom readouts,\n"
            "and every repository consumer through ``YangMillsCore``. Passing is only\n"
            "the D1/metric prefix: it does not yet prove the regional Green decay, the\n"
            "four actions, uniform B0/delta0, window 15, ``20/41`` or ``TermSource``.\n",
        ),
        (
            "c6d-source-separated-ambient-green-v3",
            "c6d-post-green-decay-prefix-v3",
        ),
        (
            "hrpoly-c6d-source-separated-ambient-green",
            "hrpoly-c6d-post-green-decay-prefix",
        ),
        (
            "03_c6d_source_green_yang_mills_core_root",
            "03_c6d_post_green_decay_prefix_yang_mills_core_root",
        ),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_POST_GREEN_RUNNER_REPLACEMENT_MISSING")
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
        "C6D_POST_GREEN_DECAY_PREFIX_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=5 stages=5 axiom_blocks=10 "
        "root=YangMillsCore "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
