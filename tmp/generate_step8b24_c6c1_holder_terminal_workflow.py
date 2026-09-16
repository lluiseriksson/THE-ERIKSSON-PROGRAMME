#!/usr/bin/env python3
"""Generate the cold terminal workflow for Step 8b.24 C6c.1 H1--H2d3."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
HOLDER = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b24_c6c1_holder_validation_runner.py")
)
TERMINAL = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b23_ae_terminal_workflow.py")
)
BRICKS: tuple[tuple[str, int], ...] = HOLDER["BRICKS"]


def generate(source_sha: str) -> str:
    paths: list[str] = HOLDER["source_paths"]()
    return TERMINAL["generate_for_scope"](
        source_sha,
        paths=paths,
        bricks=BRICKS,
        required_prevalidation=set(paths),
        forbidden_prevalidation=set(),
        workflow_name="Validate Step 8b.24 C6c.1 Holder H1-H2d3",
        job_id="step8b24-c6c1-holder",
        archive_stem="step8b24-c6c1-holder",
        expected_axioms=30,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".github" / "workflows" / "validate-localized-carrier.yml",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "STEP8B24_C6C1_HOLDER_TERMINAL_WORKFLOW_GENERATED "
        f"source_sha={args.source_sha} files=18 bricks=9 stages=18 "
        f"axiom_blocks=30 sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
