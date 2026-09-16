#!/usr/bin/env python3
"""Generate the one cold terminal workflow for Step-8b.24 H3--H5."""
from __future__ import annotations
import argparse,hashlib,runpy
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
H=runpy.run_path(str(ROOT/"tmp"/"generate_step8b24_c6c1_h3_h5_validation_runner.py"))
T=runpy.run_path(str(ROOT/"tmp"/"generate_step8b23_ae_terminal_workflow.py"))
BRICKS=H["BRICKS"]
def static_check():
    H["static_check"]()
    paths=H["source_paths"]()
    if len(paths)!=38 or len(set(paths))!=38: raise SystemExit("H3_H5_WORKFLOW_SCOPE_DRIFT")
    if len(BRICKS)!=19: raise SystemExit("H3_H5_WORKFLOW_BRICK_DRIFT")
    if sum(count for _,count in BRICKS)!=60: raise SystemExit("H3_H5_WORKFLOW_AXIOM_TOTAL_DRIFT")
    print("STEP8B24_H3_H5_TERMINAL_WORKFLOW_STATIC_OK files=38 bricks=19 stages=38 axiom_blocks=60")
def generate(source_sha):
    paths=H["source_paths"]()
    return T["generate_for_scope"](source_sha,paths=paths,bricks=BRICKS,
      required_prevalidation=set(paths),forbidden_prevalidation=set(),
      workflow_name="Validate Step 8b.24 H3-H5",job_id="step8b24-h3-h5",
      archive_stem="step8b24-h3-h5",expected_axioms=60)
def main():
    p=argparse.ArgumentParser();p.add_argument("--static-check",action="store_true");p.add_argument("--source-sha");p.add_argument("--output",type=Path,default=ROOT/".github"/"workflows"/"validate-localized-carrier.yml");a=p.parse_args()
    if a.static_check: static_check()
    if not a.source_sha:
        if a.static_check:return 0
        raise SystemExit("SOURCE_SHA_REQUIRED")
    content=generate(a.source_sha);a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(content,encoding="utf-8",newline="\n")
    print(f"STEP8B24_H3_H5_TERMINAL_WORKFLOW_GENERATED source_sha={a.source_sha} files=38 bricks=19 stages=38 axiom_blocks=60 sha256={hashlib.sha256(content.encode()).hexdigest().upper()} output={a.output}");return 0
if __name__=="__main__":raise SystemExit(main())
