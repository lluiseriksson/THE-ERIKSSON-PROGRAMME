#!/usr/bin/env python3
"""Fail-closed tests for the H3c product-telescope overlay."""

from __future__ import annotations

import importlib.util
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "prepare_step8b24_c6c1_h3c_product_telescope_overlay.py"


def load_module():
    spec = importlib.util.spec_from_file_location("h3c_product", SCRIPT)
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
    assert payload["declarations"] == payload["axiom_prints"] == 5
    assert payload["positive_mass_premise"] == "ABSENT"
    assert payload["holder_numerator"] == "UNSPLIT"
    assert payload["contour_direction"] == "TRANSPORT_DISPLACEMENT_ONLY"
    source = rows[0][1].decode()
    must_fail(
        lambda: module.require_semantics(
            source.replace("(ha : 0 ≤ a) (hrho : 0 ≤ rho)",
              "(ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)", 1)
        ),
        "positive mass reintroduced",
    )
    must_fail(
        lambda: module.require_semantics(
            source.replace("SignType.sign (transportDisplacement nu)",
              "SignType.sign (holderDisplacement nu)", 1)
        ),
        "wrong contour direction",
    )
    audit = module.INPUTS[1][0].read_text(encoding="utf-8")
    must_fail(
        lambda: module.shared.promote(
            audit.replace("#print axioms ", "-- removed ", 1), 5, True
        ),
        "missing axiom readout",
    )
    with tempfile.TemporaryDirectory(prefix="h3c-product-") as tmp:
        tampered = Path(tmp) / "tampered.lean"
        tampered.write_bytes(module.INPUTS[0][0].read_bytes() + b"\n")
        must_fail(
            lambda: module.shared.read_pinned(tampered, module.INPUTS[0][1]),
            "input drift",
        )
    print(
        "PASS H3c overlay self-test: mass + direction + axiom + hash gates; "
        f"elapsed_seconds={time.perf_counter() - started:.6f}; "
        f"peak_rss_bytes={module.shared.peak_rss_bytes()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
