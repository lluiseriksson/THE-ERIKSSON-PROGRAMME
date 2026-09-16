#!/usr/bin/env python3
"""Lightweight fail-closed test for the Step 8b.24 extension runner."""

from __future__ import annotations

import hashlib
from pathlib import Path
import runpy
import textwrap


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "tmp" / "generate_step8b24_extension_validation_runner.py"
WORKFLOW_PATH = ROOT / "tmp" / "generate_step8b24_extension_terminal_workflow.py"
module = runpy.run_path(str(MODULE_PATH))
workflow = runpy.run_path(str(WORKFLOW_PATH))
globals_ = module["generate"].__globals__
SOURCE = "a" * 40


def good_blob(_sha: str, path: str) -> bytes:
    old_source, old_audit = module["pair_paths"](module["OLD_OWNER"])
    neutral_source, _ = module["pair_paths"](module["BRICKS"][4][0])
    if path == old_source:
        return b"import Mathlib\n\ntheorem old_owner_kept : True := by trivial\n"
    if path == old_audit:
        return (
            "import Mathlib\n\n"
            f"#print axioms YangMills.RG.{module['MOVED_THEOREM']}\n"
        ).encode()
    body = "import Mathlib\n\n/-! PRE-VALIDATION: synthetic. -/\n"
    if path == neutral_source:
        body += f"theorem {module['MOVED_THEOREM']} : True := by trivial\n"
    return body.encode()


def terminal_good_blob(sha: str, path: str) -> bytes:
    prerequisites, validation = workflow["source_scope"]()
    if path in prerequisites:
        return f"import Mathlib\n\n-- sealed prerequisite {path}\n".encode()
    if path not in validation:
        raise AssertionError(f"unexpected terminal path: {path}")
    return good_blob(sha, path)


def main() -> int:
    globals_["git"] = lambda *args, **kwargs: SOURCE
    globals_["blob"] = good_blob
    text: str = module["generate"](SOURCE)
    compile(text, "generated_step8b24_extension_runner.py", "exec")
    assert len(module["BRICKS"]) == 17
    assert len(module["source_paths"]()) == 36
    assert sum(count for _, count in module["BRICKS"]) == 49
    assert text.count("'lake', 'build'") == 18
    assert text.count("'lake', 'env', 'lean'") == 18
    assert "05b_old_owner_focal" in text
    assert "05b_old_owner_audit" in text
    assert "        4," in text

    terminal_module = workflow["generate"].__globals__["TERMINAL"]
    terminal_globals = terminal_module["generate_for_scope"].__globals__
    terminal_globals["blob"] = terminal_good_blob
    workflow_text: str = workflow["generate"](SOURCE)
    assert workflow_text.count("lake build YangMills.RG.") == 18
    assert workflow_text.count("lake env lean YangMills/RG/") == 18
    assert "test \"$(wc -l < evidence/source-blobs.sha256)\" -eq 80" in workflow_text
    assert "if total != 53:" in workflow_text
    assert "step8b24-extension-evidence.tar.gz" in workflow_text
    start = workflow_text.index("          python - <<'PY'\n") + len("          python - <<'PY'\n")
    end = workflow_text.index("\n          PY", start)
    compile(
        textwrap.dedent(workflow_text[start:end]),
        "generated_step8b24_extension_axiom_gate.py",
        "exec",
    )
    prerequisite = workflow["source_scope"]()[0][0]
    original_terminal_blob = terminal_globals["blob"]
    terminal_globals["blob"] = lambda sha, path: (
        b"import Mathlib\n/-! PRE-VALIDATION: forbidden prerequisite. -/\n"
        if path == prerequisite else original_terminal_blob(sha, path)
    )
    try:
        workflow["generate"](SOURCE)
    except SystemExit as error:
        assert "PREREQUISITE_NOT_SEALED" in str(error)
    else:
        raise AssertionError("terminal workflow accepted an unsealed prerequisite")
    terminal_globals["blob"] = original_terminal_blob
    old_source, _ = module["pair_paths"](module["OLD_OWNER"])
    terminal_globals["blob"] = lambda sha, path: (
        (f"theorem {module['MOVED_THEOREM']} : True := by trivial\n").encode()
        if path == old_source else original_terminal_blob(sha, path)
    )
    try:
        workflow["generate"](SOURCE)
    except SystemExit as error:
        assert "OLD_OWNER_STILL_DECLARES_MOVED_THEOREM" in str(error)
    else:
        raise AssertionError("terminal workflow accepted duplicate theorem ownership")
    terminal_globals["blob"] = original_terminal_blob

    original = globals_["blob"]
    globals_["blob"] = lambda sha, path: (
        (f"theorem {module['MOVED_THEOREM']} : True := by trivial\n").encode()
        if path == old_source else original(sha, path)
    )
    try:
        module["generate"](SOURCE)
    except SystemExit as error:
        assert "OLD_OWNER_STILL_DECLARES_MOVED_THEOREM" in str(error)
    else:
        raise AssertionError("ownership tamper did not fail closed")

    print(
        "STEP8B24_EXTENSION_RUNNER_SELFTEST_OK runner=pass workflow=pass "
        "new_bricks=17 validated_pairs=18 files=36 stages=36 "
        "axiom_blocks=53 ownership_tamper=fail_closed "
        "generator_sha256=" + hashlib.sha256(MODULE_PATH.read_bytes()).hexdigest().upper()
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
