#!/usr/bin/env python3
"""Colab diagnostic gate for the signed-alias affine Fourier-negation carry.

The immutable mathematical source is ``SOURCE_SHA``. This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol. Its queue contains
only the signed-alias carry module and its three-declaration audit.

Honest scope: this seals no endpoint phase, finite-to-continuous
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
    "signed_alias_fourier_neg_carry_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-signed-alias-fourier-neg-carry-v1"
runner.SOURCE_SHA = "e73cd91d00e0f241c0b772cb84888d47b34d2df8"
runner.ROOT = Path("/content/hrpoly-signed-alias-fourier-neg-carry")
runner.EVIDENCE = Path("/content/hrpoly-signed-alias-fourier-neg-carry-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-signed-alias-fourier-neg-carry-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-signed-alias-fourier-neg-carry-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceSignedAliasFourierNegCarry.lean":
        "d44a8f64a6ec081ce026bf022332a2008bc27d49894e856294838088631c153b",
    "YangMills/RG/BalabanCMP99SourceSignedAliasFourierNegCarryAudit.lean":
        "a4b45c0e5e963f6487befc1a75cc21d059c5ee78dce8feb272aa91c8f4ab9e0b",
}

runner.QUEUE = [
    (
        "signed_alias_fourier_neg_carry_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceSignedAliasFourierNegCarry",
        ],
        None,
    ),
    (
        "signed_alias_fourier_neg_carry_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceSignedAliasFourierNegCarryAudit.lean",
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
