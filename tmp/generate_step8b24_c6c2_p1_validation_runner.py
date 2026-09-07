#!/usr/bin/env python3
"""Generate the fresh-Colab validator for the promoted C6c.2 P1 pair."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
BASE = runpy.run_path(str(ROOT / "tmp/generate_step8b24_c6c2_p0_validation_runner.py"))
MODULE = "BalabanCMP99SourcePrefixPoincare"
AXIOM_BLOCKS = 8


def generate(source_sha: str) -> str:
    base_generate = BASE["generate"]
    globals_ = base_generate.__globals__
    old_module = globals_["MODULE"]
    old_axioms = globals_["AXIOM_BLOCKS"]
    try:
        globals_["MODULE"] = MODULE
        globals_["AXIOM_BLOCKS"] = AXIOM_BLOCKS
        content = base_generate(source_sha)
    finally:
        globals_["MODULE"] = old_module
        globals_["AXIOM_BLOCKS"] = old_axioms
    replacements = (
        ("Step 8b.24/C6c.2 P0 only", "Step 8b.24/C6c.2 P1 only", 1),
        (
            "canonical retained-prefix construction and its exact\n"
            "ten-readout sibling audit.  It does not introduce P1--P5",
            "prefix Poincare monotonicity construction and its exact\n"
            "eight-readout sibling audit.  It does not introduce P2--P5", 1,
        ),
        ("step8b24_c6c2_p0_base", "step8b24_c6c2_p1_base", 1),
        ("step8b24-c6c2-p0-v1", "step8b24-c6c2-p1-v1", 1),
        ("hrpoly-step8b24-c6c2-p0", "hrpoly-step8b24-c6c2-p1", 4),
        ("01_p0_canonical_prefix_tower_focal", "01_p1_prefix_poincare_focal", 1),
        ("02_p0_canonical_prefix_tower_audit", "02_p1_prefix_poincare_audit", 1),
    )
    for old, new, expected in replacements:
        if content.count(old) != expected:
            raise SystemExit(
                f"P1_RUNNER_TEMPLATE_MARKER_COUNT={old!r}/"
                f"{content.count(old)}/{expected}"
            )
        content = content.replace(old, new)
    compile(content, "generated_step8b24_c6c2_p1_validation.py", "exec")
    return content


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "scripts/colab_step8b24_c6c2_p1_validation.py",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "STEP8B24_C6C2_P1_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=2 bricks=1 stages=2 "
        f"axiom_blocks={AXIOM_BLOCKS} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
