#!/usr/bin/env python3
"""Synthetic fail-closed checks for the P0--P9 executed-notebook auditor."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "p0_p9_notebook_audit", HERE / "audit_p0_p9_executed_notebook.py"
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load notebook auditor")
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


def transcript() -> str:
    rows = [
        f"RUNNER_TRANSPORT_SHA256={audit.RUNNER_SHA256}",
        f"BASE_RUNNER_TRANSPORT_SHA256={audit.BASE_RUNNER_SHA256}",
        f"P0_P9_PATHS_TRANSPORT_SHA256={audit.PATHS_SHA256}",
        f"P0_P9_MANIFEST_TRANSPORT_SHA256={audit.MANIFEST_SHA256}",
        f"RUNNER_REV={audit.RUNNER_REV}",
        "RUNTIME=CPU RAM_GIB=50.99",
        f"HEAD is now at {audit.SOURCE_SHA[:9]}",
        "LEAN_OVERLAY_TEXT_OK files=39",
        "LEAN_IMPORT_PREFIX_OK files=39",
    ]
    for stage in sorted(audit.REQUIRED_CORE_STAGES | audit.expected_queue_stages()):
        rows.append(f"STAGE={stage} EXIT=0 SECONDS=1.000")
    rows.extend("depends on axioms: [propext, Quot.sound]" for _ in range(199))
    rows.extend(
        [
            "EVIDENCE_SHA256=" + "1" * 64,
            "EVIDENCE_ARCHIVE_SHA256=" + "2" * 64,
            "FINAL_STATUS=PASS",
            "LAUNCHER_EXIT=0",
            "LAUNCHER_RUNTIME_RELEASE_REQUESTED=1",
        ]
    )
    return "\n".join(rows) + "\n"


def notebook(text: str, *, count: int | None = 1) -> dict[str, object]:
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": count,
                "metadata": {},
                "outputs": [{"name": "stdout", "output_type": "stream", "text": text}],
                "source": ["# immutable launcher\n"],
            }
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def write(path: Path, payload: dict[str, object]) -> None:
    path.write_text(json.dumps(payload), encoding="utf-8")


def expect_fail(path: Path) -> None:
    try:
        audit.audit(path)
    except ValueError:
        return
    raise AssertionError(f"fixture unexpectedly passed: {path.name}")


with tempfile.TemporaryDirectory() as directory:
    root = Path(directory)
    good = root / "good.ipynb"
    write(good, notebook(transcript()))
    result = audit.audit(good)
    assert result.startswith("P0_P9_EXECUTED_NOTEBOOK_OK ")

    bad_status = root / "bad-status.ipynb"
    write(bad_status, notebook(transcript().replace("FINAL_STATUS=PASS", "FINAL_STATUS=FAIL")))
    expect_fail(bad_status)

    forbidden = root / "forbidden.ipynb"
    write(forbidden, notebook(transcript().replace("Quot.sound", "sorryAx", 1)))
    expect_fail(forbidden)

    missing = root / "missing-stage.ipynb"
    first_stage = sorted(audit.expected_queue_stages())[0]
    write(missing, notebook(transcript().replace(f"STAGE={first_stage} EXIT=0 SECONDS=1.000\n", "")))
    expect_fail(missing)

    duplicate = root / "duplicate-run.ipynb"
    payload = notebook(transcript())
    payload["cells"].append(dict(payload["cells"][0]))
    write(duplicate, payload)
    expect_fail(duplicate)

print("P0_P9_EXECUTED_NOTEBOOK_SELFTEST_OK")
