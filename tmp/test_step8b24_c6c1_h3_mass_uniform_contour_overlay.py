#!/usr/bin/env python3
"""Fail-closed tests for H3a/H3b mass-uniform contour overlay."""

from __future__ import annotations

import importlib.util
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "prepare_step8b24_c6c1_h3_mass_uniform_contour_overlay.py"


def load_module():
    spec = importlib.util.spec_from_file_location("h3_mass_uniform", SCRIPT)
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
    assert len(rows) == 6
    assert payload["declarations"] == payload["axiom_prints"] == 10
    assert payload["positive_mass_premise"] == "ABSENT"
    assert payload["polydisc_gate"] == "ALL_COORDINATES"
    assert payload["fine_lattice_displacements"] == "BOTH_LITERAL"
    assert payload["product_telescope"] == "OPEN"
    periodicity = rows[0][1].decode()
    holomorphy = rows[2][1].decode()
    shift = rows[4][1].decode()
    must_fail(
        lambda: module.require_semantics(
            periodicity,
            holomorphy.replace(
                "(ha : 0 ≤ a) (hrho : 0 ≤ rho)",
                "(ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)",
                1,
            ),
            shift,
        ),
        "positive mass reintroduced",
    )
    must_fail(
        lambda: module.require_semantics(
            periodicity,
            holomorphy,
            shift.replace("himag : ∀ k", "himag : ∀ k = nu", 1),
        ),
        "one-coordinate-only strip gate",
    )
    must_fail(
        lambda: module.require_semantics(
            periodicity.replace(
                "cmp89Eq249PhysicalFineLatticeDisplacement", "cmp89Eq251LatticeDisplacement"
            ),
            holomorphy,
            shift,
        ),
        "unit-lattice displacement substituted",
    )
    audit = module.INPUTS[1][0].read_text(encoding="utf-8")
    must_fail(
        lambda: module.shared.promote(
            audit.replace("#print axioms ", "-- removed ", 1), 7, True
        ),
        "missing axiom readout",
    )
    with tempfile.TemporaryDirectory(prefix="h3-mass-uniform-") as tmp:
        tampered = Path(tmp) / "tampered.lean"
        tampered.write_bytes(module.INPUTS[0][0].read_bytes() + b"\n")
        must_fail(
            lambda: module.shared.read_pinned(tampered, module.INPUTS[0][1]),
            "input drift",
        )
    print(
        "PASS H3 mass-uniform overlay self-test: mass + polydisc + axiom + hash gates; "
        f"elapsed_seconds={time.perf_counter() - started:.6f}; "
        f"peak_rss_bytes={module.shared.peak_rss_bytes()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
