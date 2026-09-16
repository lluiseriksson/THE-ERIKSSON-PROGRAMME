#!/usr/bin/env python3
"""Colab diagnostic gate for the generated Green one-mode Fourier fibre.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol.  Its sole queue is the
Gate-7 one-mode Fourier specialization and its four-declaration audit.  It
does not prove a continuous Brillouin integral, a regional Green bound, a
uniform ``B0``, or attainment of window 15.
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
SPEC = importlib.util.spec_from_file_location("gate7_fourier_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "gate7-generated-green-fourier-v3"
runner.SOURCE_SHA = "65545ad3084c38831ed3f8bc02124c7d49de3d89"
runner.ROOT = Path("/content/hrpoly-gate7-generated-green-fourier")
runner.EVIDENCE = Path("/content/hrpoly-gate7-generated-green-fourier-evidence")
runner.ARCHIVE = Path("/content/hrpoly-gate7-generated-green-fourier-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-gate7-generated-green-fourier-paths.txt")

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierMode.lean":
        "7c24e402dbc4f9d5761bb90a4869fdc73b846742003c857e3902acea931e8166",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierModeAudit.lean":
        "d2ccb839a72db990c1d014d373b85228f290befee643bb8b1cb37c26f10ea25a",
}

runner.QUEUE = [
    (
        "generated_green_fourier_mode_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierMode",
        ],
        None,
    ),
    (
        "generated_green_fourier_mode_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierModeAudit.lean",
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
