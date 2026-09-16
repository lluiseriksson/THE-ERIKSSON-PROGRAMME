#!/usr/bin/env python3
"""Fail-closed tests for the H5d0a--H5d0b deterministic overlay."""

from __future__ import annotations

import importlib.util
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "prepare_step8b24_c6c1_h5_holder_factor_overlay.py"


def load_module():
    spec = importlib.util.spec_from_file_location("h5_holder_factor_prepare", SCRIPT)
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
    assert payload["declarations"] == 7
    assert payload["axiom_prints"] == 7
    assert payload["general_alpha_literal"] is True
    assert payload["alpha_zero_identity"] is True
    assert payload["xi_rpow_inverse_extracted_before_norm"] is True
    assert payload["positive_mass_premise"] == "ABSENT"
    assert payload["generated_operator"] == "OPEN"
    assert payload["tsum_transport"] == "OPEN"
    assert payload["owner_metric_dictionary"] == "OPEN"

    source = module.INPUTS[0][0].read_text(encoding="utf-8")
    audit = module.INPUTS[1][0].read_text(encoding="utf-8")
    must_fail(
        lambda: module.promote(source + "\ntheorem injected := by sorry\n", 4, False),
        "sorry injection",
    )
    must_fail(
        lambda: module.promote(
            source.replace("(mass a alpha : ℝ)",
                "(mass a alpha : ℝ) (hmassPos : 0 < mass)", 1),
            4,
            False,
        ),
        "positive mass premise",
    )
    must_fail(
        lambda: module.promote(audit.replace("#print axioms ", "-- removed ", 1), 4, True),
        "missing axiom readout",
    )
    factor = rows[0][1].decode("utf-8")
    integral = rows[2][1].decode("utf-8")
    must_fail(
        lambda: module.require_holder_semantics(
            factor,
            integral.replace("integral_const_mul c _", "integral_zero", 1),
        ),
        "factor not extracted through integral before norm",
    )
    must_fail(
        lambda: module.require_holder_semantics(
            factor,
            integral.replace(
                "cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha",
                "cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a 0",
            ),
        ),
        "general alpha erased from literal integral",
    )
    with tempfile.TemporaryDirectory(prefix="h5-holder-factor-overlay-") as tmp:
        tampered = Path(tmp) / "tampered.lean"
        tampered.write_bytes(module.INPUTS[0][0].read_bytes() + b"\n")
        must_fail(
            lambda: module.read_pinned(tampered, module.INPUTS[0][1]),
            "input blob drift",
        )

    print(
        "PASS H5 holder-factor overlay self-test: alpha + alpha0 + pre-norm + "
        "mass + sorry + axiom + hash gates; "
        f"elapsed_seconds={time.perf_counter() - started:.6f}; "
        f"peak_rss_bytes={module.peak_rss_bytes()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
