#!/usr/bin/env python3
"""Generate the fail-closed canonical ambient-completion verifier."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RUNNER = ROOT / "scripts" / "colab_c6d_canonical_ambient_completion_validation.py"
DEFAULT_NOTEBOOK = ROOT / "scripts" / "colab_c6d_canonical_ambient_completion_validation.ipynb"
DEFAULT_OUTPUT = ROOT / "tmp" / "verify_c6d_canonical_ambient_completion_evidence.py"


def notebook_cell_source(path: Path) -> str:
    notebook = json.loads(path.read_text(encoding="utf-8"))
    cells = [cell for cell in notebook.get("cells", []) if cell.get("cell_type") == "code"]
    if len(cells) != 1:
        raise RuntimeError(f"C6D_CANONICAL_VERIFIER_NOTEBOOK_CODE_CELLS={len(cells)}")
    source = cells[0].get("source")
    if isinstance(source, list):
        return "".join(source)
    if isinstance(source, str):
        return source
    raise RuntimeError("C6D_CANONICAL_VERIFIER_NOTEBOOK_SOURCE_INVALID")


def runner_metadata(path: Path) -> tuple[str, str, dict[str, str]]:
    text = path.read_text(encoding="utf-8")
    source = re.search(r"(?m)^runner\.SOURCE_SHA = ['\"]([0-9a-f]{40})['\"]$", text)
    revision = re.search(r"(?m)^runner\.RUNNER_REV = ['\"]([^'\"]+)['\"]$", text)
    blobs = re.search(
        r"(?ms)^runner\.SOURCE_BLOBS = (\{.*?\})\nrunner\.QUEUE =",
        text,
    )
    if source is None or revision is None or blobs is None:
        raise RuntimeError("C6D_CANONICAL_VERIFIER_RUNNER_METADATA_MISSING")
    parsed = ast.literal_eval(blobs.group(1))
    if not isinstance(parsed, dict) or not all(
        isinstance(key, str) and isinstance(value, str)
        for key, value in parsed.items()
    ):
        raise RuntimeError("C6D_CANONICAL_VERIFIER_SOURCE_BLOBS_INVALID")
    return source.group(1), revision.group(1), parsed


def generated_text(source_sha: str, runner: Path, notebook: Path) -> str:
    runner_source, runner_rev, blobs = runner_metadata(runner)
    if runner_source != source_sha:
        raise RuntimeError(
            f"C6D_CANONICAL_VERIFIER_SOURCE={runner_source} EXPECTED={source_sha}"
        )
    canonical_blobs = json.dumps(blobs, sort_keys=True, separators=(",", ":"))
    blobs_sha = hashlib.sha256(canonical_blobs.encode()).hexdigest().upper()
    cell_source = notebook_cell_source(notebook)
    cell_sha = hashlib.sha256(cell_source.encode()).hexdigest().upper()
    return f'''#!/usr/bin/env python3
"""Fail-closed verifier specialization for canonical ambient completion."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
SOURCE_SHA = "{source_sha}"
RUNNER_REV = "{runner_rev}"
SOURCE_BLOBS_COUNT = {len(blobs)}
SOURCE_BLOBS_SHA256 = "{blobs_sha}"
NOTEBOOK_CELL_SOURCE_SHA256 = "{cell_sha}"
SUCCESS_SENTINEL = "C6D_CANONICAL_AMBIENT_COMPLETION_EVIDENCE_OK"
MODULES = [
    "BalabanCMP99ActiveRegionCanonicalAmbientCompletion",
    "BalabanCMP99Eq360C6dCanonicalAmbientCompletion",
]
AUDIT_STAGES = {{
    MODULES[0]: "01_cmp99activeregioncanonicalambientcompletion_audit",
    MODULES[1]: "02_cmp99eq360c6dcanonicalambientcompletion_audit",
}}
EXPECTED_AXIOM_HEADERS = {{MODULES[0]: 9, MODULES[1]: 2}}
QUEUE_STAGES = [
    "01_cmp99activeregioncanonicalambientcompletion_focal",
    "01_cmp99activeregioncanonicalambientcompletion_audit",
    "02_cmp99eq360c6dcanonicalambientcompletion_focal",
    "02_cmp99eq360c6dcanonicalambientcompletion_audit",
    "03_c6d_canonical_ambient_completion_yang_mills_core_root",
]


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_completion_evidence_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_CANONICAL_COMPLETION_VERIFIER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    base = load_base()
    base.SOURCE_SHA = SOURCE_SHA
    base.RUNNER_REV = RUNNER_REV
    base.SOURCE_BLOBS_COUNT = SOURCE_BLOBS_COUNT
    base.SOURCE_BLOBS_SHA256 = SOURCE_BLOBS_SHA256
    base.NOTEBOOK_CELL_SOURCE_SHA256 = NOTEBOOK_CELL_SOURCE_SHA256
    base.SUCCESS_SENTINEL = SUCCESS_SENTINEL
    base.MODULES = MODULES
    base.AUDIT_STAGES = AUDIT_STAGES
    base.EXPECTED_AXIOM_HEADERS = EXPECTED_AXIOM_HEADERS
    base.QUEUE_STAGES = QUEUE_STAGES
    return base.main()


if __name__ == "__main__":
    raise SystemExit(main())
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner", type=Path, default=DEFAULT_RUNNER)
    parser.add_argument("--notebook", type=Path, default=DEFAULT_NOTEBOOK)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    content = generated_text(
        args.source_sha,
        args.runner.resolve(),
        args.notebook.resolve(),
    )
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "C6D_CANONICAL_AMBIENT_COMPLETION_VERIFIER_GENERATED "
        f"source_sha={args.source_sha} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
