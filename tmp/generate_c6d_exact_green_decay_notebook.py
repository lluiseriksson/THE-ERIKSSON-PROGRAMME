#!/usr/bin/env python3
"""Generate the one-cell Colab launcher for exact C6d Green decay."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_eq359_complex_one_scale_average_notebook.py"
RUNNER_PATH = "scripts/colab_c6d_exact_green_decay_validation.py"
OUTPUT = ROOT / "scripts" / "colab_c6d_exact_green_decay_validation.ipynb"


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_exact_green_decay_notebook_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_EXACT_GREEN_DECAY_NOTEBOOK_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-checkpoint", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    content = load_base().generate(
        args.source_sha,
        args.runner_checkpoint,
        args.runner_rev,
        runner_path=RUNNER_PATH,
        retain_runtime=True,
    )
    notebook = json.loads(content)
    cells = [cell for cell in notebook["cells"] if cell.get("cell_type") == "code"]
    if len(cells) != 1:
        raise RuntimeError(f"C6D_EXACT_GREEN_DECAY_NOTEBOOK_CODE_CELLS={len(cells)}")
    source = cells[0]["source"]
    compile("".join(source) if isinstance(source, list) else source, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "C6D_EXACT_GREEN_DECAY_NOTEBOOK_GENERATED "
        f"source_sha={args.source_sha} runner_checkpoint={args.runner_checkpoint} "
        f"runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
