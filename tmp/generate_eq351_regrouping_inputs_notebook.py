#!/usr/bin/env python3
"""Generate the one-cell launcher for the canonical Eq. (3.51) input gate."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_eq359_complex_one_scale_average_notebook.py"
RUNNER_PATH = "scripts/colab_eq351_regrouping_inputs_validation.py"
OUTPUT = ROOT / "scripts" / "colab_eq351_regrouping_inputs_validation.ipynb"


def load_base():
    spec = importlib.util.spec_from_file_location(
        "eq351_regrouping_inputs_notebook_base", BASE
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("EQ351_REGROUPING_INPUTS_NOTEBOOK_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-checkpoint", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--retain-runtime", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    base = load_base()
    content = base.generate(
        args.source_sha,
        args.runner_checkpoint,
        args.runner_rev,
        runner_path=RUNNER_PATH,
        retain_runtime=args.retain_runtime,
    )
    notebook = json.loads(content)
    compile("".join(notebook["cells"][0]["source"]), str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "EQ351_REGROUPING_INPUTS_NOTEBOOK_GENERATED "
        f"source_sha={args.source_sha} "
        f"runner_checkpoint={args.runner_checkpoint} "
        f"runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
