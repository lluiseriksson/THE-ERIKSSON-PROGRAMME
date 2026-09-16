#!/usr/bin/env python3
"""Fail-closed tests for the H4a/H4b deterministic overlay preparation."""

from __future__ import annotations

import importlib.util
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "prepare_step8b24_c6c1_h4_swap_overlay.py"


def load_module():
    spec = importlib.util.spec_from_file_location("h4_swap_prepare", SCRIPT)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def must_fail(callable_, label: str) -> None:
    try:
        callable_()
    except AssertionError:
        return
    raise AssertionError(f"expected fail-closed rejection: {label}")


def main() -> int:
    started = time.perf_counter()
    module = load_module()

    rows, payload = module.build_payload()
    assert len(rows) == 2
    assert payload["status"] == "PRE-VALIDATION"
    assert payload["compiler_verified"] is False
    assert payload["declarations"] == 12
    assert payload["axiom_prints"] == 7
    assert payload["source_metric_dictionary"] == "OPEN"
    assert payload["complete_holder_bound"] == "OPEN"
    assert payload["physical_fine_displacements"] == "BOTH_LITERAL"

    source_text = module.SOURCE_DRAFT.read_bytes().decode("utf-8")
    audit_text = module.AUDIT_DRAFT.read_bytes().decode("utf-8")
    must_fail(
        lambda: module.promote_source(source_text + "\ntheorem injected := by sorry\n"),
        "sorry injection",
    )
    must_fail(
        lambda: module.promote_audit(
            audit_text.replace(
                "#print axioms YangMills.RG.cmp89Eq251EuclideanNorm_neg\n", "", 1
            )
        ),
        "missing axiom readout",
    )
    must_fail(
        lambda: module.promote_source(
            source_text.replace(
                "cmp89Eq249PhysicalFineLatticeDisplacement xi",
                "cmp89Eq251LatticeDisplacement",
            )
        ),
        "unit-lattice displacement substitution",
    )

    with tempfile.TemporaryDirectory(prefix="h4-swap-overlay-") as tmp:
        tampered = Path(tmp) / "tampered.lean"
        tampered.write_bytes(module.SOURCE_DRAFT.read_bytes() + b"\n")
        must_fail(
            lambda: module.read_pinned(tampered, module.SOURCE_INPUT_SHA256),
            "input blob drift",
        )

    print(
        "PASS H4 swap overlay self-test: positive + sorry + axiom + hash gates; "
        f"elapsed_seconds={time.perf_counter() - started:.6f}; "
        f"peak_rss_bytes={module.peak_rss_bytes()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
