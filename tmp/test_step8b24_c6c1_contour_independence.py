#!/usr/bin/env python3
"""Fail-closed self-test for the static H3/H4 contour-prefix auditor."""

from __future__ import annotations

import copy
import importlib.util
import shutil
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
AUDITOR = HERE / "audit_step8b24_c6c1_contour_independence.py"


def load_auditor():
    spec = importlib.util.spec_from_file_location("contour_audit", AUDITOR)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def copy_fixture(module, root: Path) -> None:
    target = root / "tmp"
    target.mkdir()
    for name in list(module.FILES) + list(module.AUDITS):
        shutil.copy2(HERE / name, target / name)


def must_fail(callable_, label: str) -> None:
    try:
        callable_()
    except AssertionError:
        return
    raise AssertionError(f"expected fail-closed rejection: {label}")


def main() -> int:
    started = time.perf_counter()
    module = load_auditor()
    original = copy.deepcopy(module.FILES)
    original_audits = copy.deepcopy(module.AUDITS)
    with tempfile.TemporaryDirectory(prefix="contour-audit-") as tmp:
        root = Path(tmp)
        copy_fixture(module, root)

        result = module.audit(root)
        assert result["status"] == "PASS"
        assert result["source_files"] == 5
        assert result["audit_files"] == 5
        assert result["declarations"] == 24
        assert result["axiom_blocks"] == 19
        assert result["compiler_verified"] is False

        name = "BalabanCMP89Eq249CompleteHolderEndpointSwap.draft.lean"
        path = root / "tmp" / name
        pristine = path.read_bytes()

        path.write_bytes(pristine + b"\n-- holderSeminorm in a comment is harmless\n")
        module.FILES[name]["sha256"] = module.sha256(path.read_bytes())
        assert module.audit(root)["status"] == "PASS"

        path.write_bytes(pristine + b"\ndef holderSeminorm := 0\n")
        module.FILES[name]["sha256"] = module.sha256(path.read_bytes())
        must_fail(lambda: module.audit(root), "forbidden seminorm code")

        needle = b"import YangMills.RG.BalabanCMP89Eq251ComplexContourPhase\n"
        assert needle in pristine
        path.write_bytes(pristine.replace(needle, b"", 1))
        module.FILES[name]["sha256"] = module.sha256(path.read_bytes())
        must_fail(lambda: module.audit(root), "missing required import")

        path.write_bytes(pristine)
        module.FILES = copy.deepcopy(original)
        assert module.audit(root)["status"] == "PASS"

        audit_name = "BalabanCMP89Eq249CompleteHolderEndpointSwapAudit.draft.lean"
        audit_path = root / "tmp" / audit_name
        audit_pristine = audit_path.read_bytes()
        audit_path.write_bytes(audit_pristine.replace(
            b"#print axioms YangMills.RG.cmp89Eq251EuclideanNorm_neg\n", b"", 1
        ))
        module.AUDITS[audit_name]["sha256"] = module.sha256(audit_path.read_bytes())
        must_fail(lambda: module.audit(root), "missing axiom readout")

        audit_path.write_bytes(audit_pristine)
        module.AUDITS = copy.deepcopy(original_audits)
        assert module.audit(root)["status"] == "PASS"

    print(
        "PASS contour-independence self-test: "
        "positive + comment + semantic + import gates; "
        f"elapsed_seconds={time.perf_counter() - started:.6f}; "
        f"peak_rss_bytes={module.peak_rss_bytes()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
