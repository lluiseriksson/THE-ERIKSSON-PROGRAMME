#!/usr/bin/env python3
"""Colab diagnostic gate for Step-7b item 5, gate 5.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime auto-release.  Its sole queue is the
physical stabilized-denominator nonvanishing module and its five-declaration
audit.  It does not identify the generated Green or attain window 15.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
SPEC = importlib.util.spec_from_file_location("item5_gate5_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "item5-stabilized-denominator-v2"
runner.SOURCE_SHA = "c99e2bbd4d8b3c24462a59f68b4cbbc3b5ddad81"
runner.ROOT = Path("/content/hrpoly-item5-stabilized-denominator")
runner.EVIDENCE = Path("/content/hrpoly-item5-stabilized-denominator-evidence")
runner.ARCHIVE = Path("/content/hrpoly-item5-stabilized-denominator-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-item5-stabilized-denominator-paths.txt")

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing.lean":
        "515dc3865264dfae973d3cad627f14a450cc40a6a2638b1a7e75c00031f13b91",
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishingAudit.lean":
        "9135c10d79ccb18b0719800c565d14d3abe43bbc4c5252488bded9e238cb06bc",
}

runner.QUEUE = [
    (
        "physical_stabilized_denominator_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing",
        ],
        None,
    ),
    (
        "physical_stabilized_denominator_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishingAudit.lean",
        ],
        5,
    ),
]


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    raise SystemExit(runner.main())
