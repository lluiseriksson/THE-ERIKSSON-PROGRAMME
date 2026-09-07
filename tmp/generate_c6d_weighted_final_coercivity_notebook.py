#!/usr/bin/env python3
"""Generate the retained one-cell launcher for the combined C6d gate."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_c6d_weighted_final_prefix_notebook.py"
RUNNER_PATH = "scripts/colab_c6d_weighted_final_coercivity_validation.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_weighted_final_coercivity_validation.ipynb"


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_wfc_notebook_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_WFC_NOTEBOOK_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def generate(source_sha: str, runner_checkpoint: str, runner_rev: str) -> str:
    base = load_base()
    base.RUNNER_PATH = RUNNER_PATH
    return base.generate(source_sha, runner_checkpoint, runner_rev)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-checkpoint", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    content = generate(args.source_sha, args.runner_checkpoint, args.runner_rev)
    notebook = json.loads(content)
    compile("".join(notebook["cells"][0]["source"]), str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "C6D_WEIGHTED_FINAL_COERCIVITY_NOTEBOOK_GENERATED "
        f"source_sha={args.source_sha} runner_checkpoint={args.runner_checkpoint} "
        f"runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
