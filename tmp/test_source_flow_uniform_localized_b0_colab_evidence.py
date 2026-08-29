#!/usr/bin/env python3
"""Focused self-test for the uniform/localized B0 notebook transcript gate."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_source_flow_uniform_localized_b0_colab_evidence.py"
CELL_SOURCE = (
    "import urllib.request, hashlib\n"
    "URL = 'https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/a754e28555270ebbdab8bff05f262368a39c43fa/"
    "scripts/colab_source_flow_uniform_point_source_b0_validation.py'\n"
    "EXPECTED = '2563bfba3de16b09733d2ae751a7f39ed0d29282386857ef51f8ed0767a29021'\n"
    "payload = urllib.request.urlopen(URL, timeout=60).read()\n"
    "measured = hashlib.sha256(payload).hexdigest()\n"
    "print('LAUNCHER_SHA256=' + measured, flush=True)\n"
    "if measured != EXPECTED:\n"
    "    raise RuntimeError('LAUNCHER_HASH_MISMATCH')\n"
    "exec(compile(payload, URL, 'exec'), {'__name__': '__main__'})\n"
)


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
    output = (
        f"LAUNCHER_SHA256={verifier.LAUNCHER_SHA256}\n"
        "FINAL_STATUS=PASS\n"
        "EVIDENCE_DOWNLOAD_REQUESTED=1\n"
        "RUNTIME_UNASSIGN_REQUESTED=1\n"
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
