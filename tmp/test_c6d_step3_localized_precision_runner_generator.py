#!/usr/bin/env python3
"""Lightweight fail-closed test for the future C6d Step3 runner generator."""

from __future__ import annotations

import hashlib
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "tmp" / "generate_c6d_step3_localized_precision_validation_runner.py"
module = runpy.run_path(str(MODULE_PATH))
globals_ = module["generate"].__globals__
SOURCE = "a" * 40


def good_blob(_sha: str, path: str) -> bytes:
    paths = module["source_paths"]()
    if path == module["PATH_MANIFEST"]:
        return ("\n".join(paths) + "\n").encode()
    if path == module["ROOT_MODULE"]:
        return b"import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision\n"
    for brick, expected in module["BRICKS"]:
        source, audit = module["pair_paths"](brick)
        if path == source:
            declarations = "\n".join(
                f"theorem {name.rsplit('.', 1)[-1]} : True := by trivial"
                for name in expected
            )
            return (
                "import Mathlib\n"
                "/-! PRE-VALIDATION: synthetic; not compiler-verified. -/\n"
                + declarations + "\n"
            ).encode()
        if path == audit:
            prints = "\n".join(f"#print axioms {name}" for name in expected)
            return (
                f"import YangMills.RG.{brick}\n"
                "/-! PRE-VALIDATION: synthetic audit; not compiler-verified. -/\n"
                + prints + "\n"
            ).encode()
    raise AssertionError(f"unexpected blob path: {path}")


def main() -> int:
    globals_["git"] = lambda *args, **kwargs: SOURCE
    globals_["blob"] = good_blob
    text: str = module["generate"](SOURCE)
    compile(text, "generated_c6d_step3_runner.py", "exec")
    assert len(module["source_paths"]()) == 6
    assert len(module["BRICKS"]) == 3
    assert sum(len(names) for _, names in module["BRICKS"]) == 11
    assert text.count("'lake', 'build'") == 4
    assert text.count("'lake', 'env', 'lean'") == 3
    assert "check_lean_axiom_readout_coverage.py" in text
    assert "c6d-step3-localized-precision-v1" in text
    assert "YangMillsCore" in text
    assert "files.download(str(runner.ARCHIVE))" in text

    original = globals_["blob"]
    first = module["source_paths"]()[0]
    globals_["blob"] = lambda sha, path: (
        original(sha, path).replace(b"PRE-VALIDATION:", b"PREVALIDATION:")
        if path == first else original(sha, path)
    )
    try:
        module["generate"](SOURCE)
    except SystemExit as error:
        assert "C6D_STEP3_PREVALIDATION_COUNT" in str(error)
    else:
        raise AssertionError("runner accepted a missing PRE-VALIDATION marker")

    first_audit = module["pair_paths"](module["BRICKS"][0][0])[1]
    globals_["blob"] = lambda sha, path: (
        original(sha, path).replace(b"#print axioms ", b"#print axioms bogus.", 1)
        if path == first_audit else original(sha, path)
    )
    try:
        module["generate"](SOURCE)
    except SystemExit as error:
        assert "C6D_STEP3_AUDIT_SCOPE_MISMATCH" in str(error)
    else:
        raise AssertionError("runner accepted a changed audit surface")

    print(
        "C6D_STEP3_RUNNER_SELFTEST_OK files=8 bricks=3 stages=8 "
        "axiom_blocks=11 root=YangMillsCore tamper=fail_closed "
        "generator_sha256=" + hashlib.sha256(MODULE_PATH.read_bytes()).hexdigest().upper()
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
