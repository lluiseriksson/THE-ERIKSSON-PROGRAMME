#!/usr/bin/env python3
"""Fail-closed audit of the single-cell P0--P9 Colab transcript.

This checker does not compile Lean.  It verifies that an executed notebook is
the output of the immutable v2 launcher and that the runner itself reported a
complete PASS for the exact 39-file source checkpoint.  A green transcript is
still intermediate compiler evidence, not a terminal hRpoly result.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
PATHS = ROOT / "tmp" / "P0-P9-SCRATCH-PATHS.txt"
SOURCE_SHA = "fecf2f768f049b59743a6b2df8a7d569748254c1"
RUNNER_SHA256 = "1c607bac9523d60cafc53770f933997fcd7c4559e15ec7e05b69fd88d714edda"
BASE_RUNNER_SHA256 = "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
PATHS_SHA256 = "fec594c0fba52e14f8cc1e1ba886202fcdf2e425de2c93e56dbf59feebb2fa61"
MANIFEST_SHA256 = "d5b829cb109e8062a19b9f57a9a9a7346170652d51582f05ac731636595c9325"
RUNNER_REV = "p0-p9-prefix-combes-thomas-v2"
EXPECTED_AXIOM_BLOCKS = 199
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_CORE_STAGES = {
    "download_toolchain",
    "extract_toolchain",
    "lean_version",
    "lake_version",
    "clone",
    "checkout",
    "head",
    "overlay_text_guard",
    "import_prefix_guard",
    "lake_update",
    "mathlib_pin",
    "cache_get",
    "p0_p9_static_gate",
    "p0_p9_static_selftest",
    "p0_p9_materialize_project_prerequisites",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def output_text(notebook: dict[str, object]) -> tuple[str, int]:
    cells = notebook.get("cells")
    if not isinstance(cells, list):
        raise ValueError("notebook cells missing")
    executed = 0
    chunks: list[str] = []
    for cell in cells:
        if not isinstance(cell, dict) or cell.get("cell_type") != "code":
            continue
        if cell.get("execution_count") is not None:
            executed += 1
        outputs = cell.get("outputs", [])
        if not isinstance(outputs, list):
            raise ValueError("code-cell outputs malformed")
        for output in outputs:
            if not isinstance(output, dict):
                raise ValueError("output entry malformed")
            if output.get("output_type") == "stream":
                text = output.get("text", "")
                chunks.extend(text if isinstance(text, list) else [str(text)])
            elif output.get("output_type") == "error":
                chunks.append("\n".join(map(str, output.get("traceback", []))))
    return "".join(chunks), executed


def expected_queue_stages() -> set[str]:
    payload = PATHS.read_bytes()
    if sha256(payload) != PATHS_SHA256:
        raise ValueError("local immutable path-list digest drift")
    paths = [line for line in payload.decode("utf-8-sig").splitlines() if line]
    if len(paths) != 39 or len(set(paths)) != 39:
        raise ValueError(f"local immutable path-list scope={len(paths)}/{len(set(paths))}")
    result: set[str] = set()
    for index, relative in enumerate(paths, start=1):
        stem = Path(relative).stem
        suffix = re.sub(r"[^A-Za-z0-9]+", "_", stem).lower()
        result.add(f"p0_p9_{index:02d}_{suffix}")
    return result


def require_once(text: str, literal: str) -> None:
    count = text.count(literal)
    if count != 1:
        raise ValueError(f"marker count {count}, expected 1: {literal}")


def audit(path: Path) -> str:
    notebook_bytes = path.read_bytes()
    notebook = json.loads(notebook_bytes.decode("utf-8"))
    text, executed = output_text(notebook)
    if executed != 1:
        raise ValueError(f"executed code-cell count={executed}, expected 1")

    for literal in (
        f"RUNNER_TRANSPORT_SHA256={RUNNER_SHA256}",
        f"BASE_RUNNER_TRANSPORT_SHA256={BASE_RUNNER_SHA256}",
        f"P0_P9_PATHS_TRANSPORT_SHA256={PATHS_SHA256}",
        f"P0_P9_MANIFEST_TRANSPORT_SHA256={MANIFEST_SHA256}",
        f"RUNNER_REV={RUNNER_REV}",
        f"HEAD is now at {SOURCE_SHA[:9]}",
        "RUNTIME=CPU RAM_GIB=",
        "LEAN_OVERLAY_TEXT_OK files=39",
        "LEAN_IMPORT_PREFIX_OK files=39",
        "FINAL_STATUS=PASS",
        "LAUNCHER_EXIT=0",
        "LAUNCHER_RUNTIME_RELEASE_REQUESTED=1",
    ):
        require_once(text, literal)

    ram = re.search(r"RUNTIME=CPU RAM_GIB=([0-9]+(?:\.[0-9]+)?)", text)
    if ram is None or float(ram.group(1)) < 40:
        raise ValueError("high-RAM CPU runtime not proved")
    for forbidden in (
        "FINAL_STATUS=FAIL",
        "FIRST_ERROR=",
        "FORBIDDEN_AXIOM=",
        "AXIOM_BLOCK_COUNT=",
        "sorryAx",
        "ofReduceBool",
    ):
        if forbidden in text:
            raise ValueError(f"forbidden transcript marker: {forbidden}")

    stage_rows = re.findall(
        r"STAGE=([a-z0-9_]+) EXIT=([-0-9]+) SECONDS=([0-9]+(?:\.[0-9]+)?)",
        text,
    )
    stages: dict[str, tuple[int, str]] = {}
    for stage, exit_code, seconds in stage_rows:
        if stage in stages:
            raise ValueError(f"duplicate stage result: {stage}")
        stages[stage] = (int(exit_code), seconds)
    expected = REQUIRED_CORE_STAGES | expected_queue_stages()
    missing = sorted(expected - stages.keys())
    if missing:
        raise ValueError(f"missing stage results: {missing}")
    failed = sorted(stage for stage, (code, _) in stages.items() if code != 0)
    if failed:
        raise ValueError(f"nonzero stage results: {failed}")

    compact = re.sub(r"\s+", "", text)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    if len(blocks) != EXPECTED_AXIOM_BLOCKS:
        raise ValueError(
            f"axiom block count={len(blocks)}, expected={EXPECTED_AXIOM_BLOCKS}"
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise ValueError(f"axiom block {index}={sorted(names)}")

    evidence = re.findall(r"EVIDENCE_SHA256=([0-9a-f]{64})", text)
    archive = re.findall(r"EVIDENCE_ARCHIVE_SHA256=([0-9a-f]{64})", text)
    if len(evidence) != 1 or len(archive) != 1:
        raise ValueError("unique evidence hashes not proved")
    transcript_hash = sha256(text.encode("utf-8"))
    notebook_hash = sha256(notebook_bytes)
    return (
        "P0_P9_EXECUTED_NOTEBOOK_OK "
        f"source_sha={SOURCE_SHA} stages={len(stages)} queue_stages=39 "
        f"axiom_blocks={len(blocks)} evidence_sha256={evidence[0]} "
        f"archive_sha256={archive[0]} transcript_sha256={transcript_hash} "
        f"notebook_sha256={notebook_hash}"
    )


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: audit_p0_p9_executed_notebook.py EXECUTED.ipynb")
    try:
        print(audit(Path(sys.argv[1])))
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        print(f"P0_P9_EXECUTED_NOTEBOOK_FAIL {error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
