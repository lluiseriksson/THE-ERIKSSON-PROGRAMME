#!/usr/bin/env python3
"""Generate the cold terminal workflow for the Step 8b.24 S1--C6b extension."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
STEP8B23 = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b23_f_validation_runner.py")
)
EXTENSION = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b24_extension_validation_runner.py")
)
TERMINAL = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b23_ae_terminal_workflow.py")
)
NEW_BRICKS: tuple[tuple[str, int], ...] = EXTENSION["BRICKS"]
OLD_OWNER: str = EXTENSION["OLD_OWNER"]
OLD_OWNER_AUDIT_BLOCKS: int = EXTENSION["OLD_OWNER_AUDIT_BLOCKS"]
VALIDATION_BRICKS = (
    NEW_BRICKS[:5]
    + ((OLD_OWNER, OLD_OWNER_AUDIT_BLOCKS),)
    + NEW_BRICKS[5:]
)


def source_scope() -> tuple[list[str], list[str]]:
    ae, unit_f = STEP8B23["source_paths"]()
    prerequisites = ae + unit_f
    validation = EXTENSION["source_paths"]()
    if len(prerequisites) != 44 or len(validation) != 36:
        raise RuntimeError("Step 8b.24 terminal scope count mismatch")
    if set(prerequisites) & set(validation):
        raise RuntimeError("Step 8b.24 prerequisite/validation overlap")
    return prerequisites, validation


def generate(source_sha: str) -> str:
    prerequisites, validation = source_scope()
    old_paths = set(EXTENSION["pair_paths"](OLD_OWNER))
    new_paths = set(validation) - old_paths
    if len(new_paths) != 34 or len(old_paths) != 2:
        raise RuntimeError("Step 8b.24 PRE-VALIDATION partition mismatch")
    terminal_globals = TERMINAL["generate_for_scope"].__globals__
    blob = terminal_globals["blob"]
    neutral_path, _ = EXTENSION["pair_paths"](NEW_BRICKS[4][0])
    old_path, old_audit_path = EXTENSION["pair_paths"](OLD_OWNER)
    moved = EXTENSION["MOVED_THEOREM"]
    decl = EXTENSION["DECL"]
    neutral_text = blob(source_sha, neutral_path).decode("utf-8")
    old_text = blob(source_sha, old_path).decode("utf-8")
    old_audit_text = blob(source_sha, old_audit_path).decode("utf-8")
    if decl.findall(neutral_text).count(moved) != 1:
        raise SystemExit("NEUTRAL_OWNER_DOES_NOT_DECLARE_MOVED_THEOREM_ONCE")
    if moved in decl.findall(old_text):
        raise SystemExit("OLD_OWNER_STILL_DECLARES_MOVED_THEOREM")
    if f"#print axioms YangMills.RG.{moved}" not in old_audit_text:
        raise SystemExit("OLD_OWNER_AUDIT_DROPPED_MOVED_THEOREM_READOUT")
    forbidden = set(prerequisites) | old_paths
    return TERMINAL["generate_for_scope"](
        source_sha,
        paths=prerequisites + validation,
        bricks=VALIDATION_BRICKS,
        required_prevalidation=new_paths,
        forbidden_prevalidation=forbidden,
        workflow_name="Validate Step 8b.24 S1-C6b extension",
        job_id="step8b24-extension",
        archive_stem="step8b24-extension",
        expected_axioms=53,
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
        "STEP8B24_EXTENSION_TERMINAL_WORKFLOW_GENERATED "
        f"source_sha={args.source_sha} prerequisites=44 validation_files=36 "
        f"new_bricks=17 validated_pairs=18 stages=36 axiom_blocks=53 "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
