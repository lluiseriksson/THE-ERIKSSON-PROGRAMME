#!/usr/bin/env python3
"""Lightweight fail-closed self-test for the Step 8b.23 A--E generators."""

from __future__ import annotations

import contextlib
import io
from pathlib import Path
import runpy
import textwrap


ROOT = Path(__file__).resolve().parents[1]
runner = runpy.run_path(str(ROOT / "tmp" / "generate_step8b23_ae_validation_runner.py"))
workflow = runpy.run_path(str(ROOT / "tmp" / "generate_step8b23_ae_terminal_workflow.py"))
paths: list[str] = runner["source_paths"]()


def good_blob(_sha: str, path: str) -> bytes:
    return (
        "import Mathlib\n\n"
        "/-!\nPRE-VALIDATION: synthetic generator self-test only.\n-/\n"
        f"-- {path}\n"
    ).encode()


def expect_failure(callable_: object, marker: str) -> None:
    try:
        with contextlib.redirect_stderr(io.StringIO()):
            callable_()  # type: ignore[operator]
    except SystemExit as error:
        if marker not in str(error):
            raise AssertionError(f"wrong fail-closed marker: {error}") from error
    else:
        raise AssertionError(f"expected fail-closed marker: {marker}")


def main() -> int:
    assert len(paths) == 36
    assert len(runner["BRICKS"]) == 18
    assert sum(count for _, count in runner["BRICKS"]) == 124

    runner_globals = runner["generate"].__globals__
    workflow_globals = workflow["generate"].__globals__
    runner_globals["git"] = lambda *args, **kwargs: "a" * 40
    runner_globals["blob"] = good_blob
    runner_text: str = runner["generate"]("a" * 40)
    compile(runner_text, "generated_step8b23_ae_runner.py", "exec")
    assert runner_text.count("'lake', 'build'") == 18
    assert runner_text.count("'lake', 'env', 'lean'") == 18
    assert "CenteredPeriodicL1ResidueSum" not in runner_text
    assert runner_text.count("PRE-VALIDATION") == 0
    assert "runner.run = run_with_persistent_log" in runner_text
    assert 'files.download(str(runner.ARCHIVE))' in runner_text
    assert 'print("EVIDENCE_DOWNLOAD_REQUESTED=1"' in runner_text

    original_runner_blob = runner_globals["blob"]
    runner_globals["blob"] = lambda sha, path: b"import Mathlib\n"
    expect_failure(lambda: runner["generate"]("a" * 40), "MISSING_PRE_VALIDATION")
    runner_globals["blob"] = original_runner_blob

    workflow_globals["blob"] = good_blob
    workflow_text: str = workflow["generate"]("b" * 40)
    assert workflow_text.count("lake build YangMills.RG.") == 18
    assert workflow_text.count("lake env lean YangMills/RG/") == 18
    assert workflow_text.count("PRE-VALIDATION") == 0
    assert "CenteredPeriodicL1ResidueSum" not in workflow_text
    assert "test \"$(wc -l < evidence/source-blobs.sha256)\" -eq 36" in workflow_text
    assert "if total != 124:" in workflow_text
    assert "FINAL_STATUS=PASS\\n" in workflow_text

    start = workflow_text.index("          python - <<'PY'\n") + len("          python - <<'PY'\n")
    end = workflow_text.index("\n          PY", start)
    verifier = textwrap.dedent(workflow_text[start:end])
    compile(verifier, "generated_step8b23_ae_axiom_gate.py", "exec")

    original_workflow_blob = workflow_globals["blob"]
    workflow_globals["blob"] = lambda sha, path: b"import Mathlib\n"
    expect_failure(lambda: workflow["generate"]("b" * 40), "MISSING_PRE_VALIDATION")
    workflow_globals["blob"] = original_workflow_blob

    print(
        "STEP8B23_AE_GENERATOR_SELFTEST_OK "
        "runner=pass workflow=pass tamper=fail_closed "
        "files=36 bricks=18 stages=36 axiom_blocks=124"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
