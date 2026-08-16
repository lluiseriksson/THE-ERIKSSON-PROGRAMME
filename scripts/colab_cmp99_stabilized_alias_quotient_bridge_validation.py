#!/usr/bin/env python3
"""Colab diagnostic gate for the stabilized-to-quotient bridge.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only reproduction checks the exact
quotient cancellation used by the two endpoint solutions before the expensive
project focal.

Honest scope: this validates reduced-denominator parity/periodicity and
stabilized-solution cancellation under explicit non-singularity.  It does not
validate stabilized-denominator periodicity, the affine cross-fibre carry,
the complete physical sum, regional ``B0``, window 15 or a terminal field.
"""

from __future__ import annotations

import hashlib
import importlib.util
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
    "cmp99_stabilized_alias_quotient_bridge_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-stabilized-alias-quotient-bridge-v4"
runner.SOURCE_SHA = "839727ffa9b21fd683c23558dac0211374cefdd8"
runner.ROOT = Path("/content/hrpoly-cmp99-stabilized-alias-quotient-bridge")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-stabilized-alias-quotient-bridge-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-stabilized-alias-quotient-bridge-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-stabilized-alias-quotient-bridge-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceStabilizedAliasQuotientBridge.lean":
        "97d4780f50271eec24c1df523f49e0439056181338c3a044c5b1ea7ea824b67e",
    "YangMills/RG/BalabanCMP99SourceStabilizedAliasQuotientBridgeAudit.lean":
        "8d2f7f222bb824e08ceae8adf4293418f4ca9c5fede3d7a85f48758ef1625647",
}

REPRO = HERE / "cmp99_stabilized_alias_quotient_bridge_repro.lean"
REPRO.write_text(
    """import Mathlib

example (central row fine reduced stabilized : ℂ)
    (hcentral : central ≠ 0) (hfine : fine ≠ 0)
    (hreduced : reduced ≠ 0)
    (hstable : central * reduced = stabilized) :
    central * row / (fine * stabilized) = row / (fine * reduced) := by
  rw [← hstable]
  field_simp [hcentral, hfine, hreduced]
  rw [mul_comm central, mul_assoc, mul_inv_cancel₀ hcentral, mul_one]
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "cmp99_stabilized_alias_quotient_bridge_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "cmp99_stabilized_alias_quotient_bridge_focal",
        [
            "lake",
            "build",
            "YangMills.RG."
            "BalabanCMP99SourceStabilizedAliasQuotientBridge",
        ],
        None,
    ),
    (
        "cmp99_stabilized_alias_quotient_bridge_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceStabilizedAliasQuotientBridgeAudit.lean",
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
