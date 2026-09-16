#!/usr/bin/env python3
"""Generate the single cold terminal workflow for Step 8b.23 Unit F.

The source checkpoint must contain sealed Units A--E and PRE-VALIDATION Unit
F.  The workflow validates only the four Unit-F focal/audit pairs, while its
blob gate fixes both the 36 immutable prerequisites and the eight new files.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
F_RUNNER = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b23_f_validation_runner.py")
)
TERMINAL = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b23_ae_terminal_workflow.py")
)
BRICKS: tuple[tuple[str, int], ...] = F_RUNNER["BRICKS"]


def generate(source_sha: str) -> str:
    ae, unit_f = F_RUNNER["source_paths"]()
    paths = ae + unit_f
    return TERMINAL["generate_for_scope"](
        source_sha,
        paths=paths,
        bricks=BRICKS,
        required_prevalidation=set(unit_f),
        forbidden_prevalidation=set(ae),
        workflow_name="Validate Step 8b.23 Unit F",
        job_id="step8b23-f",
        archive_stem="step8b23-f",
        expected_axioms=49,
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
        "STEP8B23_F_TERMINAL_WORKFLOW_GENERATED "
        f"source_sha={args.source_sha} prerequisites=36 unit_f_files=8 "
        f"bricks=4 stages=8 axiom_blocks=49 "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
