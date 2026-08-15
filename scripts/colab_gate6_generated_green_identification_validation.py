#!/usr/bin/env python3
"""Colab diagnostic gate for the generated physical Green endpoint.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime auto-release.  Its sole queue is the
generated Green identification module and its four-declaration audit.  It
does not prove a regional Green bound or attain window 15.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
SPEC = importlib.util.spec_from_file_location("gate6_green_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "gate6-generated-green-v2"
runner.SOURCE_SHA = "10c80c3579de6f84f6686462e52cf23bf22bb761"
runner.ROOT = Path("/content/hrpoly-gate6-generated-green")
runner.EVIDENCE = Path("/content/hrpoly-gate6-generated-green-evidence")
runner.ARCHIVE = Path("/content/hrpoly-gate6-generated-green-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-gate6-generated-green-paths.txt")

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentification.lean":
        "3120ad19f781f98e143812672ccef8293b0879639e465edb6de30ad0026d5661",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentificationAudit.lean":
        "aece1c37a834af9d9afdc7ef58af0d11fc4dfef7bd3bf9934141f3cc5240475c",
}

runner.QUEUE = [
    (
        "generated_green_identification_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentification",
        ],
        None,
    ),
    (
        "generated_green_identification_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentificationAudit.lean",
        ],
        4,
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
