#!/usr/bin/env python3
"""Colab diagnostic gate for the mass-uniform CMP89 complex floor.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol.  Its sole queue is the
three-theorem mass-uniform complex floor and its audit.  It does not prove the
mass window is preserved by the RG flow, attain the scalar complex window,
construct a regional ``B0``, attain window 15, or inhabit ``TermSource``.
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
SPEC = importlib.util.spec_from_file_location("mass_uniform_floor_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp89-mass-uniform-complex-floor-v1"
runner.SOURCE_SHA = "733ecbb60d43b72e04f9740eb825251b397503b8"
runner.ROOT = Path("/content/hrpoly-cmp89-mass-uniform-complex-floor")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-mass-uniform-complex-floor-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-mass-uniform-complex-floor-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-mass-uniform-complex-floor-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq249CentralStabilizedComplexFloorMassUniform.lean":
        "8b87cc9a40b2d8b951b3c16c6042dab9f040f667ff1d81f02d7b3ea05a65b75b",
    "YangMills/RG/BalabanCMP89Eq249CentralStabilizedComplexFloorMassUniformAudit.lean":
        "18d69877b2d7c5a83d261933f611edc43aaac5878e97dca0dfc0776bb3c85154",
}

runner.QUEUE = [
    (
        "cmp89_mass_uniform_complex_floor_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexFloorMassUniform",
        ],
        None,
    ),
    (
        "cmp89_mass_uniform_complex_floor_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP89Eq249CentralStabilizedComplexFloorMassUniformAudit.lean",
        ],
        3,
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
