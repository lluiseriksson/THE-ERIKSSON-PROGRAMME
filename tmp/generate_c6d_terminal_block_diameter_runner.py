#!/usr/bin/env python3
"""Generate the cold Colab runner for the typed terminal-block diameter."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_source_separated_ambient_green_validation_runner.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_terminal_block_diameter_validation.py"
MODULE = "BalabanCMP99SourceActiveRegionTerminalBlockDiameter"
DECLARATIONS = (
    "CMP99SourceActiveRegionChain.div_pow_eq_of_sameTerminalBlock",
    "CMP99SourceActiveRegionChain.sameTerminalBlock_finBoxDist_le",
    "CMP99SourceActiveRegionChain.generatedCountingMass_finiteRange_terminalBlock",
    "CMP99SourceActiveRegionChain.QprimeMass_finiteRange_terminalBlock",
)


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_terminal_diameter_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_TERMINAL_DIAMETER_RUNNER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def generate(source_sha: str) -> str:
    base = load_base()
    base.BRICKS = ((MODULE, DECLARATIONS),)
    content = base.generate(source_sha)
    replacements = (
        (
            "Fresh Colab gate for both source-carrier C6d ambient Green branches.",
            "Fresh Colab gate for the typed terminal-block diameter producer.",
        ),
        (
            "This runner validates the positive- and zero-depth source/audit pairs, all\n"
            "twenty-five public axiom readouts and every repository consumer through\n"
            "``YangMillsCore``.  Passing\n"
            "does not attain window 15, move ``20/41`` or inhabit ``TermSource``.",
            "This runner validates the typed terminal-block diameter source/audit pair,\n"
            "all four public axiom readouts and every repository consumer through\n"
            "``YangMillsCore``. Passing closes only the geometric finite-range input;\n"
            "it does not produce Green decay, attain window 15, move ``20/41`` or\n"
            "inhabit ``TermSource``.",
        ),
        (
            "c6d-source-separated-ambient-green-v3",
            "c6d-terminal-block-diameter-v3",
        ),
        (
            "hrpoly-c6d-source-separated-ambient-green",
            "hrpoly-c6d-terminal-block-diameter",
        ),
        (
            "03_c6d_source_green_yang_mills_core_root",
            "02_c6d_terminal_block_diameter_yang_mills_core_root",
        ),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_TERMINAL_DIAMETER_RUNNER_REPLACEMENT_MISSING")
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
        "C6D_TERMINAL_BLOCK_DIAMETER_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=3 stages=3 axiom_blocks=4 "
        "root=YangMillsCore "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
