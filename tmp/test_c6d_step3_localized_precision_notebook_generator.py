#!/usr/bin/env python3
"""Lightweight test for the pinned C6d Step3 Colab notebook generator."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "generate_c6d_step3_localized_precision_notebook.py"
module = runpy.run_path(str(SCRIPT))
globals_ = module["generate"].__globals__
SOURCE = "a" * 40
RUNNER = "b" * 40
RUNNER_TEXT = (
    'runner.RUNNER_REV = "c6d-step3-localized-precision-v3"\n'
    f"runner.SOURCE_SHA = {SOURCE!r}\n"
).encode()


def main() -> int:
    globals_["require_commit"] = lambda _sha, _label: None
    globals_["blob"] = lambda _checkpoint, _path: RUNNER_TEXT
    content: str = module["generate"](SOURCE, RUNNER)
    notebook = json.loads(content)
    assert len(notebook["cells"]) == 1
    assert notebook["cells"][0]["outputs"] == []
    cell = "".join(notebook["cells"][0]["source"])
    compile(cell, "generated_c6d_step3_notebook.py", "exec")
    assert SOURCE not in cell
    assert RUNNER in cell
    assert hashlib.sha256(RUNNER_TEXT).hexdigest() in cell
    assert "release_runtime" not in cell
    assert "RUNTIME_UNASSIGN_REQUESTED_BY_LAUNCHER=1" not in cell
    assert "RUNTIME_RETAINED_FOR_EVIDENCE=1" in cell

    globals_["blob"] = lambda _checkpoint, _path: RUNNER_TEXT.replace(
        SOURCE.encode(), ("c" * 40).encode()
    )
    try:
        module["generate"](SOURCE, RUNNER)
    except SystemExit as error:
        assert "RUNNER_SOURCE_PIN_MISMATCH" in str(error)
    else:
        raise AssertionError("notebook accepted a runner pinned to another source")

    globals_["blob"] = lambda _checkpoint, _path: RUNNER_TEXT.replace(
        b"c6d-step3-localized-precision-v3", b"c6d-step3-localized-precision-v4"
    )
    try:
        module["generate"](SOURCE, RUNNER)
    except SystemExit as error:
        assert "RUNNER_REV_MISMATCH" in str(error)
    else:
        raise AssertionError("notebook accepted a runner with another revision")

    print(
        "C6D_STEP3_NOTEBOOK_SELFTEST_OK one_cell=1 transport_hash=exact "
        "runtime_retention=evidence tamper=fail_closed generator_sha256="
        + hashlib.sha256(SCRIPT.read_bytes()).hexdigest().upper()
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
