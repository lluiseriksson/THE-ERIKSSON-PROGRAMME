#!/usr/bin/env python3
"""Colab diagnostic gate for Step-7b item 5, gate 4.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime auto-release.  Its sole queue is the
complete centered alias-fibre nonvanishing module and its five-declaration
audit.  It does not test the stabilized denominator or Green endpoint.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
SPEC = importlib.util.spec_from_file_location("item5_gate4_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "item5-complete-fibre-nonvanishing-v2"
runner.SOURCE_SHA = "9838dcada8c05e1afe1cb451c899fbb91150a44c"
runner.ROOT = Path("/content/hrpoly-item5-complete-fibre")
runner.EVIDENCE = Path("/content/hrpoly-item5-complete-fibre-evidence")
runner.ARCHIVE = Path("/content/hrpoly-item5-complete-fibre-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-item5-complete-fibre-paths.txt")

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCenteredAliasFibreNonvanishing.lean":
        "a2e872afed46de0493ad9883d37a5f21d9c02a61d94915502fd8d0ba4cdfbac0",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCenteredAliasFibreNonvanishingAudit.lean":
        "465f765819ba56465c8854ce9f0ba138643c22464f7365665e0992eafb1c3846",
}

runner.QUEUE = [
    (
        "complete_alias_fibre_nonvanishing_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceFlatQprimeCenteredAliasFibreNonvanishing",
        ],
        None,
    ),
    (
        "complete_alias_fibre_nonvanishing_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceFlatQprimeCenteredAliasFibreNonvanishingAudit.lean",
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
