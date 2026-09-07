#!/usr/bin/env python3
"""Lightweight fail-closed test for the Step 8b.23 Unit-F runner."""

from __future__ import annotations

import hashlib
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "tmp" / "generate_step8b23_f_validation_runner.py"
module = runpy.run_path(str(MODULE_PATH))
globals_ = module["generate"].__globals__
SOURCE = "a" * 40


def good_blob(_sha: str, path: str) -> bytes:
    ae, unit_f = module["source_paths"]()
    marker = "\n/-! PRE-VALIDATION: synthetic. -/" if path in unit_f else ""
    return f"import Mathlib{marker}\n-- {path}\n".encode()


def main() -> int:
    ae, unit_f = module["source_paths"]()
    synthetic_rows = []
    for path in ae:
        digest = hashlib.sha256(good_blob(SOURCE, path)).hexdigest()
        synthetic_rows.append(f"{digest}  {path}\n")
    globals_["EXPECTED_AE_SEALED_DIGEST"] = hashlib.sha256(
        "".join(synthetic_rows).encode()
    ).hexdigest().upper()
    globals_["git"] = lambda *args, **kwargs: SOURCE
    globals_["blob"] = good_blob

    text: str = module["generate"](SOURCE)
    compile(text, "generated_step8b23_f_runner.py", "exec")
    assert len(ae) == 36 and len(unit_f) == 8
    assert len(module["BRICKS"]) == 4
    assert sum(count for _, count in module["BRICKS"]) == 49
    assert text.count("'lake', 'build'") == 4
    assert text.count("'lake', 'env', 'lean'") == 4

    original = globals_["blob"]
    globals_["blob"] = lambda sha, path: (
        b"import Mathlib\n/-! PRE-VALIDATION: forbidden prerequisite. -/\n"
        if path == ae[0] else original(sha, path)
    )
    try:
        module["generate"](SOURCE)
    except SystemExit as error:
        assert "AE_PREREQUISITE_NOT_SEALED" in str(error)
    else:
        raise AssertionError("unsealed A--E prerequisite did not fail closed")

    globals_["blob"] = lambda sha, path: (
        (
            "import Mathlib\n"
            + ("/-! PRE-VALIDATION: synthetic. -/\n" if path in unit_f else "")
            + "/-- declaration docs -/\n"
            + "set_option linter.unusedTactic false in\n"
            + "theorem bad : True := by trivial\n"
        ).encode()
    )
    try:
        module["generate"](SOURCE)
    except SystemExit as error:
        assert "DOCSTRING_BEFORE_SCOPED_OPTION" in str(error)
    else:
        raise AssertionError("invalid scoped-option placement did not fail closed")
    globals_["blob"] = original

    print(
        "STEP8B23_F_RUNNER_SELFTEST_OK runner=pass "
        "prerequisites=36 unit_f_files=8 bricks=4 stages=8 axiom_blocks=49 "
        "unsealed_tamper=fail_closed scoped_option_tamper=fail_closed "
        "generator_sha256=" + hashlib.sha256(MODULE_PATH.read_bytes()).hexdigest().upper()
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
