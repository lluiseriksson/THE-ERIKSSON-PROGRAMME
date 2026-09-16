#!/usr/bin/env python3
"""Lightweight fail-closed test for the H4a/H4b Colab runner generator."""

from __future__ import annotations

import runpy
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "tmp" / "generate_step8b24_c6c1_h4_swap_validation_runner.py"
AUDITOR = ROOT / "tmp" / "audit_step8b24_c6c1_contour_independence.py"
module = runpy.run_path(str(GENERATOR))
globals_ = module["generate"].__globals__
SOURCE = "a" * 40


def good_blob(_sha: str, path: str) -> bytes:
    if path.endswith("Audit.lean"):
        reads = "\n".join(
            f"#print axioms YangMills.RG.synthetic_{index}" for index in range(6)
        )
        return (
            "import Mathlib\n"
            "/-! PRE-VALIDATION: synthetic audit; not checked. -/\n"
            + reads
            + "\n"
        ).encode()
    return (
        "import Mathlib\n"
        "/-! PRE-VALIDATION: synthetic source; not checked.\n"
        "No CMP95, HolderSeminorm, regionalB0 or TermSource is produced. -/\n"
        "theorem synthetic_source : True := by trivial\n"
    ).encode()


def must_fail(callable_, marker: str) -> None:
    try:
        callable_()
    except SystemExit as error:
        assert marker in str(error), str(error)
        return
    raise AssertionError(f"expected fail-closed rejection: {marker}")


def main() -> int:
    started = time.perf_counter()
    globals_["git"] = lambda *args, **kwargs: SOURCE
    globals_["blob"] = good_blob

    text: str = module["generate"](SOURCE)
    compile(text, "generated_step8b24_h4_swap_runner.py", "exec")
    assert len(module["source_paths"]()) == 2
    assert text.count('["lake", "build"') == 1
    assert text.count('["lake", "env", "lean"') == 1
    assert "runner.SOURCE_BLOBS = {" in text
    assert "The CMP95 seminorm carrier" in text
    assert "source/owner metric dictionary" in text
    assert "runner.SOURCE_SHA = '" + SOURCE + "'" in text

    globals_["blob"] = lambda sha, path: (
        b"import Mathlib\n-- PRE-VALIDATION marker absent\n"
        if path.endswith(".lean") and not path.endswith("Audit.lean")
        else good_blob(sha, path)
    )
    must_fail(lambda: module["generate"](SOURCE), "H4_SWAP_PRE_VALIDATION_COUNT")

    globals_["blob"] = lambda sha, path: (
        good_blob(sha, path) + b"\ndef HolderSeminorm := 0\n"
        if path.endswith(".lean") and not path.endswith("Audit.lean")
        else good_blob(sha, path)
    )
    must_fail(lambda: module["generate"](SOURCE), "H4_SWAP_FORBIDDEN_SEMANTIC_TOKEN")

    peak_rss = runpy.run_path(str(AUDITOR))["peak_rss_bytes"]()
    print(
        "PASS H4 swap runner-generator self-test: syntax + PRE + semantic gates; "
        f"elapsed_seconds={time.perf_counter() - started:.6f}; "
        f"peak_rss_bytes={peak_rss}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
