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
    transport = audit.SUPPORTED_TRANSCRIPTS[(audit.SOURCE_SHA, audit.RUNNER_REV)]
    rows = [
        f"RUNNER_TRANSPORT_SHA256={audit.RUNNER_SHA256}",
        f"BASE_RUNNER_TRANSPORT_SHA256={audit.BASE_RUNNER_SHA256}",
        f"P0_P9_PATHS_TRANSPORT_SHA256={audit.PATHS_SHA256}",
        f"P0_P9_MANIFEST_TRANSPORT_SHA256={audit.MANIFEST_SHA256}",
        f"RUNNER_REV={audit.RUNNER_REV}",
        "RUNTIME=CPU RAM_GIB=50.99",
        f"HEAD is now at {audit.SOURCE_SHA[:9]}",
        f"LEAN_OVERLAY_TEXT_OK files={transport['overlay_files']}",
        f"LEAN_IMPORT_PREFIX_OK files={transport['overlay_files']}",
    ]
    audit_stages = audit.expected_audit_stages()
    pure_pending = True
    for stage in sorted(audit.REQUIRED_CORE_STAGES | audit.expected_queue_stages()):
        rows.append(f"STAGE={stage} CMD=[]")
        count = audit_stages.get(stage, 0)
        if count:
            nonempty = count - int(pure_pending)
            rows.extend(
                "depends on axioms: [propext, Quot.sound]" for _ in range(nonempty)
            )
            if pure_pending:
                rows.append("'Fixture.pure' does not depend on any axioms")
                pure_pending = False
        rows.append(f"STAGE={stage} EXIT=0 SECONDS=1.000")
    rows.extend(
        [
            "EVIDENCE_SHA256=" + "1" * 64,
            "EVIDENCE_ARCHIVE_SHA256=" + "2" * 64,
            "FINAL_STATUS=PASS",
            "EVIDENCE_DOWNLOAD_REQUESTED=1",
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

    colab_null_count = root / "colab-null-execution-count.ipynb"
    write(colab_null_count, notebook(transcript(), count=None))
    null_result = audit.audit(colab_null_count)
    assert null_result.startswith("P0_P9_EXECUTED_NOTEBOOK_OK ")

    partial_fail = root / "partial-fail-after-p0.ipynb"
    last_stage = sorted(audit.REQUIRED_CORE_STAGES | audit.expected_queue_stages())[-1]
    partial_text = transcript().replace(
        f"STAGE={last_stage} EXIT=0 SECONDS=1.000",
        f"STAGE={last_stage} EXIT=1 SECONDS=1.000",
    ).replace("FINAL_STATUS=PASS", "FINAL_STATUS=FAIL").replace(
        "LAUNCHER_EXIT=0", "LAUNCHER_EXIT=1"
    )
    write(partial_fail, notebook(partial_text))
    partial_result = audit.audit_p0(partial_fail)
    assert partial_result.startswith("P0_EXECUTED_NOTEBOOK_OK ")

    crossed = root / "crossed-identity.ipynb"
    old_identity = sorted(audit.SUPPORTED_TRANSCRIPTS)[0]
    write(
        crossed,
        notebook(transcript().replace(audit.RUNNER_REV, old_identity[1])),
    )
    try:
        audit.audit_p0(crossed)
    except ValueError:
        pass
    else:
        raise AssertionError("crossed transcript identity accepted")

    bad_status = root / "bad-status.ipynb"
    write(bad_status, notebook(transcript().replace("FINAL_STATUS=PASS", "FINAL_STATUS=FAIL")))
    expect_fail(bad_status)

    forbidden = root / "forbidden.ipynb"
    write(forbidden, notebook(transcript().replace("Quot.sound", "sorryAx", 1)))
    expect_fail(forbidden)

    missing_pure = root / "missing-pure.ipynb"
    write(
        missing_pure,
        notebook(transcript().replace("'Fixture.pure' does not depend on any axioms\n", "")),
    )
    expect_fail(missing_pure)

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
