#!/usr/bin/env python3
"""Fail-closed tests for the H5d1--H5d3 deterministic overlay."""

from __future__ import annotations

import importlib.util
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "prepare_step8b24_c6c1_h5_generated_holder_overlay.py"


def load_module():
    spec = importlib.util.spec_from_file_location("h5_generated_prepare", SCRIPT)
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
    assert len(rows) == 4
    assert payload["compiler_verified"] is False
    assert payload["declarations"] == payload["axiom_prints"] == 5
    assert payload["derivative_and_bond_directions"] == "INDEPENDENT"
    assert payload["endpoint_bounds_subtracted"] is False
    assert payload["owner_transport"] == "OPEN"
    assert payload["regional_B0"] == "OPEN"

    tsum_source = rows[0][1].decode("utf-8")
    point_source = rows[2][1].decode("utf-8")
    must_fail(
        lambda: module.require_generated_holder_semantics(
            tsum_source.replace("(derivMu bondNu : Fin 4)", "(derivMu : Fin 4)"),
            point_source,
        ),
        "collapsed tsum directions",
    )
    must_fail(
        lambda: module.require_generated_holder_semantics(
            tsum_source,
            point_source.replace("x.shift bondNu", "x"),
        ),
        "lost target endpoint",
    )
    must_fail(
        lambda: module.require_generated_holder_semantics(
            tsum_source,
            point_source + "\nexample : ‖(0 : ℝ)‖ = 0 := by simp\n",
        ),
        "bound introduced before cancellation",
    )
    source = module.INPUTS[0][0].read_text(encoding="utf-8")
    must_fail(
        lambda: module.shared.promote(source + "\ntheorem injected := by sorry\n", 2, False),
        "sorry injection",
    )
    with tempfile.TemporaryDirectory(prefix="h5-generated-holder-") as tmp:
        tampered = Path(tmp) / "tampered.lean"
        tampered.write_bytes(module.INPUTS[0][0].read_bytes() + b"\n")
        must_fail(
            lambda: module.shared.read_pinned(tampered, module.INPUTS[0][1]),
            "input blob drift",
        )

    print(
        "PASS H5 generated-holder overlay self-test: directions + endpoint + "
        "pre-norm + sorry + hash gates; "
        f"elapsed_seconds={time.perf_counter() - started:.6f}; "
        f"peak_rss_bytes={module.shared.peak_rss_bytes()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
