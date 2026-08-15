#!/usr/bin/env python3
"""Colab diagnostic gate for the cross-fibre Euclidean quotient carry.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol.  Its queue contains
only the natural/residue quotient-carry module and its three-declaration
audit.

Honest scope: this does not construct the induced signed-alias affine map, an
endpoint phase, regional ``B0`` or window-15 attainment.
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
    "coarse_fibre_quotient_carry_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-coarse-fibre-quotient-carry-v3"
runner.SOURCE_SHA = "be86a1ccb81dd8c69599245e12b3d7a52d7dae9c"
runner.ROOT = Path("/content/hrpoly-coarse-fibre-quotient-carry")
runner.EVIDENCE = Path("/content/hrpoly-coarse-fibre-quotient-carry-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-coarse-fibre-quotient-carry-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-coarse-fibre-quotient-carry-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceCoarseFibreFourierNegQuotientCarry.lean":
        "94d28e9fcd8e9c0e0c677cbb96399d3fe4d7afdc1bb53a8362e921e49a18779b",
    "YangMills/RG/BalabanCMP99SourceCoarseFibreFourierNegQuotientCarryAudit.lean":
        "2202b0a3380b493bff9082653c6547351b6839822237f7f4f013212e431eee8b",
}

runner.QUEUE = [
    (
        "coarse_fibre_quotient_carry_focal",
        [
            "lake",
            "build",
            "YangMills.RG."
            "BalabanCMP99SourceCoarseFibreFourierNegQuotientCarry",
        ],
        None,
    ),
    (
        "coarse_fibre_quotient_carry_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceCoarseFibreFourierNegQuotientCarryAudit.lean",
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
