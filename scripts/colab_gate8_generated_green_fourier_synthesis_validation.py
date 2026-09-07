#!/usr/bin/env python3
"""Colab diagnostic gate for the pointwise finite Green synthesis.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol.  Its sole queue is the
Gate-8 finite pointwise synthesis and its two-declaration audit.  It does not
prove a continuous Brillouin integral, finite-grid periodization, a regional
Green bound, a uniform ``B0``, or attainment of window 15.
"""

from __future__ import annotations

import importlib.util
import hashlib
from pathlib import Path
import urllib.request


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
SPEC = importlib.util.spec_from_file_location("gate8_synthesis_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "gate8-generated-green-fourier-synthesis-v2"
runner.SOURCE_SHA = "0e852bb5973c34eef9cfd17cf2b0a8c0f1987658"
runner.ROOT = Path("/content/hrpoly-gate8-generated-green-fourier-synthesis")
runner.EVIDENCE = Path(
    "/content/hrpoly-gate8-generated-green-fourier-synthesis-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-gate8-generated-green-fourier-synthesis-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-gate8-generated-green-fourier-synthesis-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierSynthesis.lean":
        "70a40b91e2387d3823a6cdf3bd739afd9bb4361fad2dd1c57298bb71c121548f",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierSynthesisAudit.lean":
        "bf1d64de62d3a5165b6168ef5a09a87c3d86e01cd54b7a7ae11d22956f774d36",
}

runner.QUEUE = [
    (
        "generated_green_fourier_synthesis_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierSynthesis",
        ],
        None,
    ),
    (
        "generated_green_fourier_synthesis_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierSynthesisAudit.lean",
        ],
        2,
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
