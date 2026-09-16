#!/usr/bin/env python3
"""Colab diagnostic gate for the complete physical endpoint integrand.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only reproduction checks local
equivalence reindexing and the explicit zero/nonzero case split before the
expensive project focal.

Honest scope: this validates the complete finite-fibre endpoint-integrand
identity.  It does not identify a Brillouin integral, build regional ``B0``,
attain window 15, discharge a terminal field or inhabit ``TermSource``.
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
    "cmp99_complete_endpoint_integrand_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-complete-endpoint-integrand-v1"
runner.SOURCE_SHA = "063f4337faba31ce7e5235e8c915a24b602a33a6"
runner.ROOT = Path("/content/hrpoly-cmp99-complete-endpoint-integrand")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-complete-endpoint-integrand-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-complete-endpoint-integrand-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-complete-endpoint-integrand-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCompleteEndpointIntegrand.lean":
        "4437f382c9a19951141ff2503a69beabf41603be59751c35d79a789ffbe4bb45",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCompleteEndpointIntegrandAudit.lean":
        "144f1b3814bfe62e0e252e89169194f534f4fbf25b6e794f8c02301d9ad88b13",
}

REPRO = HERE / "cmp99_complete_endpoint_integrand_repro.lean"
REPRO.write_text(
    """import Mathlib

example {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℂ) :
    (∑ a, f (e a)) = ∑ b, f b := by
  exact Equiv.sum_comp e f

example {A : Type*} [DecidableEq A] (x z : A)
    (hz : x = z → True) (hnz : x ≠ z → True) : True := by
  by_cases h : x = z
  · exact hz h
  · exact hnz h
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "cmp99_complete_endpoint_integrand_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "cmp99_complete_endpoint_integrand_focal",
        [
            "lake",
            "build",
            "YangMills.RG."
            "BalabanCMP99SourceFlatQprimeCompleteEndpointIntegrand",
        ],
        None,
    ),
    (
        "cmp99_complete_endpoint_integrand_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceFlatQprimeCompleteEndpointIntegrandAudit.lean",
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
