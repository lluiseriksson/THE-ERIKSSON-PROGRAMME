#!/usr/bin/env python3
"""Focused self-test for the uniform/localized B0 notebook transcript gate."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_source_flow_uniform_localized_b0_colab_evidence.py"
NOTEBOOK = ROOT / "scripts" / "colab_source_flow_uniform_point_source_b0_validation.ipynb"
_notebook_payload = json.loads(NOTEBOOK.read_text(encoding="utf-8"))
CELL_SOURCE = "".join(_notebook_payload["cells"][0]["source"])


def load_verifier():
    spec = importlib.util.spec_from_file_location("uniform_b0_verifier", VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("UNIFORM_B0_SELFTEST_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def notebook(output: str, source: str = CELL_SOURCE) -> dict[str, object]:
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "source": source,
                "outputs": [
                    {"output_type": "stream", "name": "stdout", "text": output},
                    {
                        "output_type": "error",
                        "ename": "SystemExit",
                        "evalue": "0",
                        "traceback": [],
                    },
                ],
            }
        ]
    }


def must_reject(verifier, path: Path) -> None:
    try:
        verifier.executed_notebook_text(path)
    except RuntimeError:
        return
    raise AssertionError("uniform B0 notebook verifier accepted tampered evidence")


def main() -> int:
    verifier = load_verifier()
    assert verifier.PACKAGE_MATERIALIZATION_NAMES == [
        "mathlib", "plausible", "LeanSearchClient", "importGraph",
        "proofwidgets", "aesop", "Qq", "batteries", "Cli",
    ]
    assert verifier.MODE_RECORDS == {
        "lake_update": "pinned_manifest_materialization"
    }
    assert verifier.PAYLOAD_ONLY_ARCHIVE is True
    assert verifier.TRANSCRIPT_HASH_STAGES == verifier.QUEUE_STAGES
    output = (
        f"RUNNER_TRANSPORT_SHA256={verifier.RUNNER_TRANSPORT_SHA256.lower()}\n"
        "FINAL_STATUS=PASS\n"
        "EVIDENCE_DOWNLOAD_REQUESTED=1\n"
        "RUNTIME_RETAINED_FOR_EVIDENCE_DOWNLOAD=1\n"
    )
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "executed.ipynb"
        path.write_text(json.dumps(notebook(output)), encoding="utf-8")
        assert verifier.executed_notebook_text(path) == output

        path.write_text(
            json.dumps(notebook(output.replace("FINAL_STATUS=PASS", "FINAL_STATUS=FAIL"))),
            encoding="utf-8",
        )
        must_reject(verifier, path)

        path.write_text(json.dumps(notebook(output, CELL_SOURCE + "# tamper\n")), encoding="utf-8")
        must_reject(verifier, path)

    print("UNIFORM_B0_COLAB_NOTEBOOK_EVIDENCE_SELFTEST_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
