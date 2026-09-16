#!/usr/bin/env python3
"""Lightweight fail-closed test for the H1--H2d3 runner/workflow generators."""

from __future__ import annotations

import hashlib
from pathlib import Path
import runpy
import textwrap


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "tmp" / "generate_step8b24_c6c1_holder_validation_runner.py"
WORKFLOW_PATH = ROOT / "tmp" / "generate_step8b24_c6c1_holder_terminal_workflow.py"
module = runpy.run_path(str(MODULE_PATH))
workflow = runpy.run_path(str(WORKFLOW_PATH))
globals_ = module["generate"].__globals__
SOURCE = "a" * 40


def good_blob(_sha: str, path: str) -> bytes:
    return (
        "import Mathlib\n"
        "/-! PRE-VALIDATION: synthetic; compiler result not yet checked. -/\n"
        f"-- {path}\n"
    ).encode()


def main() -> int:
    paths = module["source_paths"]()
    globals_["git"] = lambda *args, **kwargs: SOURCE
    globals_["blob"] = good_blob

    text: str = module["generate"](SOURCE)
    compile(text, "generated_step8b24_holder_runner.py", "exec")
    assert len(paths) == 18
    assert len(module["BRICKS"]) == 9
    assert sum(count for _, count in module["BRICKS"]) == 30
    assert text.count("'lake', 'build'") == 9
    assert text.count("'lake', 'env', 'lean'") == 9

    terminal_module = workflow["generate"].__globals__["TERMINAL"]
    terminal_globals = terminal_module["generate_for_scope"].__globals__
    original_terminal_blob = terminal_globals["blob"]
    terminal_globals["blob"] = good_blob
    workflow_text: str = workflow["generate"](SOURCE)
    assert workflow_text.count("lake build YangMills.RG.") == 9
    assert workflow_text.count("lake env lean YangMills/RG/") == 9
    assert "test \"$(wc -l < evidence/source-blobs.sha256)\" -eq 18" in workflow_text
    assert "if total != 30:" in workflow_text
    assert "step8b24-c6c1-holder-evidence.tar.gz" in workflow_text
    start = workflow_text.index("          python - <<'PY'\n") + len("          python - <<'PY'\n")
    end = workflow_text.index("\n          PY", start)
    compile(
        textwrap.dedent(workflow_text[start:end]),
        "generated_step8b24_holder_axiom_gate.py",
        "exec",
    )

    terminal_globals["blob"] = lambda sha, path: (
        b"import Mathlib\n-- PRE-VALIDATION marker absent\n"
        if path == paths[0] else good_blob(sha, path)
    )
    try:
        workflow["generate"](SOURCE)
    except SystemExit as error:
        assert "MISSING_PRE_VALIDATION" in str(error)
    else:
        raise AssertionError("terminal workflow accepted missing PRE-VALIDATION")
    terminal_globals["blob"] = original_terminal_blob

    original = globals_["blob"]
    globals_["blob"] = lambda sha, path: (
        b"import Mathlib\n-- PRE-VALIDATION marker absent\n"
        if path == paths[0] else original(sha, path)
    )
    try:
        module["generate"](SOURCE)
    except SystemExit as error:
        assert "HOLDER_MISSING_PRE_VALIDATION" in str(error)
    else:
        raise AssertionError("runner accepted missing PRE-VALIDATION")

    print(
        "STEP8B24_C6C1_HOLDER_RUNNER_SELFTEST_OK runner=pass workflow=pass "
        "files=18 bricks=9 stages=18 axiom_blocks=30 "
        "prevalidation_tamper=fail_closed generator_sha256="
        + hashlib.sha256(MODULE_PATH.read_bytes()).hexdigest().upper()
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
