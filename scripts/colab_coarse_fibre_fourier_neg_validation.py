#!/usr/bin/env python3
"""Colab diagnostic gate for periodic negation between coarse fibres.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol.  Its queue contains
only the cross-fibre Fourier-negation bridge and its three-declaration audit.

Honest scope: this does not assert the affine quotient carry, a simple alias
reflection law, endpoint phase, regional ``B0`` or window-15 attainment.
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
    "coarse_fibre_fourier_neg_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-coarse-fibre-fourier-neg-v2"
runner.SOURCE_SHA = "80ab41f2839cf9546e19c5a12a68196e45b5d246"
runner.ROOT = Path("/content/hrpoly-coarse-fibre-fourier-neg")
runner.EVIDENCE = Path("/content/hrpoly-coarse-fibre-fourier-neg-evidence")
runner.ARCHIVE = Path("/content/hrpoly-coarse-fibre-fourier-neg-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-coarse-fibre-fourier-neg-paths.txt")

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceCoarseFibreFourierNeg.lean":
        "df6985a32c48a9b3eb44673b93e9be6be915efb3cc527aa0a7f98921c050f991",
    "YangMills/RG/BalabanCMP99SourceCoarseFibreFourierNegAudit.lean":
        "3cabe9895f86e647585b378c77f779f49e87254e7e64b6253ed563ad37beede0",
}

runner.QUEUE = [
    (
        "coarse_fibre_fourier_neg_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceCoarseFibreFourierNeg",
        ],
        None,
    ),
    (
        "coarse_fibre_fourier_neg_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceCoarseFibreFourierNegAudit.lean",
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
