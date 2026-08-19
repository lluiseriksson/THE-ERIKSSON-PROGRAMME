#!/usr/bin/env python3
"""Fail-closed transcript audit for the promoted Step 8b.24/C6c.2 P0 pair."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


SOURCE_SHA = "033469bb1a816de9979ac04867779e2fb7a196cd"
RUNNER_REV = "step8b24-c6c2-p0-v1"
RUNNER_SHA256 = "ece8159b19783edf25fcb8b49cd1cc2f86f6cad31c4e746568f468bee3c0728c"
SOURCE_STAGE = "01_p0_canonical_prefix_tower_focal"
AUDIT_STAGE = "02_p0_canonical_prefix_tower_audit"
AXIOM_HEADERS = 10
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def output_text(notebook: dict[str, object]) -> tuple[str, int]:
    cells = notebook.get("cells")
    if not isinstance(cells, list):
        raise ValueError("notebook cells missing")
    chunks: list[str] = []
    evidenced = 0
    for cell in cells:
        if not isinstance(cell, dict) or cell.get("cell_type") != "code":
            continue
        outputs = cell.get("outputs", [])
        if not isinstance(outputs, list):
            raise ValueError("code-cell outputs malformed")
        if outputs:
            evidenced += 1
        for output in outputs:
            if not isinstance(output, dict):
                raise ValueError("output entry malformed")
            if output.get("output_type") == "stream":
                payload = output.get("text", "")
                chunks.extend(payload if isinstance(payload, list) else [str(payload)])
            elif output.get("output_type") == "error":
                chunks.append("\n".join(map(str, output.get("traceback", []))))
    return "".join(chunks), evidenced


def require_once(text: str, marker: str) -> None:
    count = text.count(marker)
    if count != 1:
        raise ValueError(f"marker count {count}, expected 1: {marker}")


def stage_output(text: str, stage: str) -> str:
    command = f"STAGE={stage} CMD="
    result = f"STAGE={stage} EXIT="
    require_once(text, command)
    require_once(text, result)
    start = text.index("\n", text.index(command)) + 1
    return text[start:text.index(result, start)]


def audit(path: Path) -> str:
    payload = path.read_bytes()
    notebook = json.loads(payload.decode("utf-8"))
    text, evidenced = output_text(notebook)
    if evidenced != 1:
        raise ValueError(f"executed code-cell count={evidenced}, expected 1")
    for marker in (
        f"RUNNER_TRANSPORT_SHA256={RUNNER_SHA256}",
        f"RUNNER_REV={RUNNER_REV}",
        f"HEAD is now at {SOURCE_SHA[:9]}",
        "LEAN_OVERLAY_TEXT_OK files=2",
        "LEAN_IMPORT_PREFIX_OK files=2",
        "FINAL_STATUS=PASS",
        "LAUNCHER_EXIT=0",
    ):
        require_once(text, marker)
    ram = re.search(r"RUNTIME=CPU RAM_GIB=([0-9]+(?:\.[0-9]+)?)", text)
    if ram is None or float(ram.group(1)) < 40:
        raise ValueError("high-RAM CPU runtime not proved")
    if "FINAL_STATUS=FAIL" in text or "FIRST_ERROR=" in text:
        raise ValueError("failed-run marker in promoted P0 transcript")
    for forbidden in ("FORBIDDEN_AXIOM=", "sorryAx", "ofReduceBool"):
        if forbidden in text:
            raise ValueError(f"forbidden transcript marker: {forbidden}")

    rows = re.findall(
        r"STAGE=([a-z0-9_]+) EXIT=([-0-9]+) SECONDS=([0-9]+(?:\.[0-9]+)?)",
        text,
    )
    stages: dict[str, int] = {}
    order: list[str] = []
    for stage, exit_code, _ in rows:
        if stage in stages:
            raise ValueError(f"duplicate stage result: {stage}")
        order.append(stage)
        stages[stage] = int(exit_code)
    if any(exit_code != 0 for exit_code in stages.values()):
        raise ValueError("PASS transcript contains a nonzero stage")
    for stage in (SOURCE_STAGE, AUDIT_STAGE):
        if stages.get(stage) != 0:
            raise ValueError(f"required promoted P0 stage not green: {stage}")
    if order.index(SOURCE_STAGE) >= order.index(AUDIT_STAGE):
        raise ValueError("promoted P0 source/audit order drift")

    compact = re.sub(r"\s+", "", stage_output(text, AUDIT_STAGE))
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != AXIOM_HEADERS:
        raise ValueError(
            f"P0 axiom header count={len(blocks) + pure}, expected={AXIOM_HEADERS}"
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise ValueError(f"forbidden P0 axiom block {index}: {sorted(names)}")
    evidence = re.findall(r"EVIDENCE_SHA256=([0-9a-f]{64})", text)
    archive = re.findall(r"EVIDENCE_ARCHIVE_SHA256=([0-9a-f]{64})", text)
    if len(evidence) != 1 or len(archive) != 1:
        raise ValueError("unique evidence hashes not proved")
    return (
        "STEP8B24_C6C2_P0_EXECUTED_NOTEBOOK_OK "
        f"source_sha={SOURCE_SHA} runner_rev={RUNNER_REV} stages={len(stages)} "
        f"axiom_headers={AXIOM_HEADERS} evidence_sha256={evidence[0]} "
        f"archive_sha256={archive[0]} notebook_sha256={hashlib.sha256(payload).hexdigest()}"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("executed_notebook", type=Path)
    args = parser.parse_args()
    print(audit(args.executed_notebook))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
