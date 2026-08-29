#!/usr/bin/env python3
"""Generate the cold Colab runner for the C6d Green owner-value prefix."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_source_separated_ambient_green_validation_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_green_owner_prefix_validation.py"
BRICKS = (
    (
        "BalabanCMP99Eq342LeftDerivativeFromValueBound",
        ("cmp99Eq342_leftDerivative_blockLocalizedSupBound_of_value",),
    ),
    (
        "BalabanCMP99Eq342RightAdjointFromValueBound",
        ("cmp99Eq342_rightAdjoint_blockLocalizedSupBound_of_value",),
    ),
    (
        "BalabanCMP99Eq342LaplacianFromLeftDerivativeBound",
        ("cmp99Eq342_laplacian_blockLocalizedSupBound_of_leftDerivative",),
    ),
    (
        "BalabanCMP99Eq342LeftDerivativeAtTerminalSpacing",
        ("cmp99Eq342_leftDerivative_blockLocalizedSupBound_at_terminalSpacing",),
    ),
    (
        "BalabanCMP99Eq342RightAdjointAtTerminalSpacing",
        ("cmp99Eq342_rightAdjoint_blockLocalizedSupBound_at_terminalSpacing",),
    ),
    (
        "BalabanCMP99Eq342LaplacianAtTerminalSpacing",
        ("cmp99Eq342_laplacian_blockLocalizedSupBound_at_terminalSpacing",),
    ),
    (
        "BalabanCMP99Eq342SourceLocalizedCertificateAssembler",
        ("cmp99Eq342SourceLocalizedGreenCertificate_of_actionBounds",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputAction",
        ("norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_apply_le_sourceScale",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputActionZeroDepth",
        ("norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_apply_le_sourceScale",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecay",
        ("norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_apply_le_ownerScale",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecayZeroDepth",
        ("norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_apply_le_ownerScale",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecay",
        ("cmp99Eq360C6dSourceSeparatedAmbientGreen_blockLocalizedSupBound",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayZeroDepth",
        ("cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_blockLocalizedSupBound",),
    ),
    (
        "BalabanCMP99SourcePhysicalLocalizedRegionNonempty",
        (
            "cmp116RegionSites_nonempty_of_sourcePhysicalLocalizedCoordinates",
            "nonempty_cmp116SourcePhysicalLocalizedActiveRegion",
            "nonempty_cmp99OmegaActiveGaugeRegion_of_sourcePhysicalLocalizedCoordinates",
        ),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivative",
        ("cmp99Eq360C6dSourceSeparatedAmbientGreen_leftDerivative_blockLocalizedSupBound",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjoint",
        ("cmp99Eq360C6dSourceSeparatedAmbientGreen_rightAdjoint_blockLocalizedSupBound",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacian",
        ("cmp99Eq360C6dSourceSeparatedAmbientGreen_laplacian_blockLocalizedSupBound",),
    ),
    (
        "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthActions",
        (
            "cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_leftDerivative_blockLocalizedSupBound",
            "cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_rightAdjoint_blockLocalizedSupBound",
            "cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_laplacian_blockLocalizedSupBound",
        ),
    ),
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_green_owner_prefix_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_GREEN_OWNER_PREFIX_RUNNER_BASE_IMPORT_FAILED")
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
            "Fresh Colab gate for the exact C6d Green owner-value prefix.",
        ),
        (
            "This runner validates the positive- and zero-depth source/audit pairs, all\n"
            "twenty-five public axiom readouts and every repository consumer through\n"
            "``YangMillsCore``.  Passing\n"
            "does not attain window 15, move ``20/41`` or inhabit ``TermSource``.",
            "This runner validates six positive/zero-depth source/audit pairs from\n"
            "owner-input action through owner-distance decay and block-localized value,\n"
            "plus the three reusable literal stencil transports and their three\n"
            "explicit-terminal-spacing adapters and scalar certificate assembler, the\n"
            "localized-\n"
            "coordinate-to-regional-site bridge and the positive- and zero-depth\n"
            "physical derivative actions completing both four-action prefixes, all\n"
            "twenty-two public axiom\n"
            "readouts and every repository consumer through\n"
            "``YangMillsCore``. Passing remains per-depth: it does not prove uniform\n"
            "B0/delta0, attain window 15, move ``20/41`` or inhabit ``TermSource``.",
        ),
        (
            "c6d-source-separated-ambient-green-v3",
            "c6d-green-owner-prefix-v1",
        ),
        (
            "hrpoly-c6d-source-separated-ambient-green",
            "hrpoly-c6d-green-owner-prefix",
        ),
        (
            "03_c6d_source_green_yang_mills_core_root",
            "19_c6d_green_owner_prefix_yang_mills_core_root",
        ),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_GREEN_OWNER_PREFIX_RUNNER_REPLACEMENT_MISSING")
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
        "C6D_GREEN_OWNER_PREFIX_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=37 stages=37 axiom_blocks=22 "
        "root=YangMillsCore "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
