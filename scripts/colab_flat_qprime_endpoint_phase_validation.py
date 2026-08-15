#!/usr/bin/env python3
"""Colab diagnostic gate for the fine-to-coarse endpoint phase dictionary.

The immutable mathematical source is ``SOURCE_SHA``. This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol. Its queue contains
only the endpoint-phase module and its four-declaration audit.

Honest scope: this seals no affine-sum reindexing, finite-to-continuous
periodization, regional ``B0``, window-15 attainment or terminal field.
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
SPEC = importlib.util.spec_from_file_location(
    "flat_qprime_endpoint_phase_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-flat-qprime-endpoint-phase-v1"
runner.SOURCE_SHA = "aec4077a9d4ae7e8b8cec70719ec09c12de0c66e"
runner.ROOT = Path("/content/hrpoly-flat-qprime-endpoint-phase")
runner.EVIDENCE = Path("/content/hrpoly-flat-qprime-endpoint-phase-evidence")
runner.ARCHIVE = Path("/content/hrpoly-flat-qprime-endpoint-phase-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-flat-qprime-endpoint-phase-paths.txt")

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimeEndpointPhase.lean":
        "1af4c3a6368a12ef0e4bd444bfb3aab801ae645c5c67f49ad26ebabb557bf2c5",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeEndpointPhaseAudit.lean":
        "ec32bf2d253e0a543dc9c799b1ccc9f7fab9637ea9c9ed8f79c1f232e5028d90",
}

runner.QUEUE = [
    (
        "flat_qprime_endpoint_phase_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointPhase",
        ],
        None,
    ),
    (
        "flat_qprime_endpoint_phase_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceFlatQprimeEndpointPhaseAudit.lean",
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
