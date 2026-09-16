#!/usr/bin/env python3
"""Fail-closed tests for the H5a--H5c deterministic overlay."""

from __future__ import annotations

import importlib.util
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "prepare_step8b24_c6c1_h5_termwise_overlay.py"


def load_module():
    spec = importlib.util.spec_from_file_location("h5_termwise_prepare", SCRIPT)
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
    assert payload["declarations"] == 3
    assert payload["axiom_prints"] == 3
    assert payload["positive_mass_premise"] == "ABSENT"
    assert payload["derivative_and_bond_directions"] == "INDEPENDENT"
    assert payload["tsum_transport"] == "OPEN"
    assert payload["owner_metric_dictionary"] == "OPEN"

    source = module.INPUTS[0][0].read_text(encoding="utf-8")
    audit = module.INPUTS[1][0].read_text(encoding="utf-8")
    must_fail(
        lambda: module.promote(source + "\ntheorem injected := by sorry\n", 1, False),
        "sorry injection",
    )
    must_fail(
        lambda: module.promote(source.replace("(ha : 0 ≤ a)",
            "(ha : 0 ≤ a) (hmassPos : 0 < mass)", 1), 1, False),
        "positive mass premise",
    )
    must_fail(
        lambda: module.promote(audit.replace("#print axioms ", "-- removed ", 1), 1, True),
        "missing axiom readout",
    )
    termwise_promoted = rows[2][1].decode("utf-8")
    must_fail(
        lambda: module.require_independent_directions(
            termwise_promoted.replace("(derivMu bondNu : Fin 4)",
                "(derivMu : Fin 4)", 1)
        ),
        "collapsed derivative/bond directions",
    )
    with tempfile.TemporaryDirectory(prefix="h5-termwise-overlay-") as tmp:
        tampered = Path(tmp) / "tampered.lean"
        tampered.write_bytes(module.INPUTS[0][0].read_bytes() + b"\n")
        must_fail(
            lambda: module.read_pinned(tampered, module.INPUTS[0][1]),
            "input blob drift",
        )

    print(
        "PASS H5 termwise overlay self-test: positive + sorry + mass + "
        "independent-directions + axiom + hash gates; "
        f"elapsed_seconds={time.perf_counter() - started:.6f}; "
        f"peak_rss_bytes={module.peak_rss_bytes()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
