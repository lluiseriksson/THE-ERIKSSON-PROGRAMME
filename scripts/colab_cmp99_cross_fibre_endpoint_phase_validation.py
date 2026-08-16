#!/usr/bin/env python3
"""Colab diagnostic gate for the cross-fibre endpoint-phase transport.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only reproduction checks both the
sign transfer in the finite phase and the whole-fibre equivalence reindexing
before the expensive project focal.

Honest scope: this validates the endpoint phase, the nonzero-fibre pointwise
row-to-column sample and the complete finite physical-fibre reindexing.  It
does not handle the zero coarse fibre, identify a Brillouin integral, build a
regional ``B0``, attain window 15, discharge a terminal field or inhabit
``TermSource``.
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
    "cmp99_cross_fibre_endpoint_phase_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-cross-fibre-endpoint-phase-v3"
runner.SOURCE_SHA = "affa623b62d9238e1f64f6c8ca87cfb76444c266"
runner.ROOT = Path("/content/hrpoly-cmp99-cross-fibre-endpoint-phase")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-cross-fibre-endpoint-phase-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-cross-fibre-endpoint-phase-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-cross-fibre-endpoint-phase-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCrossFibreEndpointPhase.lean":
        "c5f1893c0f95688701174e6ead237e38f374c716c3e4c44f6e273cc1960c5d80",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCrossFibreEndpointPhaseAudit.lean":
        "eca7be0dfc0ba3f644fa44f8493be50f21e05edaaaae93d6d551d5cce3022f35",
}

REPRO = HERE / "cmp99_cross_fibre_endpoint_phase_repro.lean"
REPRO.write_text(
    """import Mathlib

example {d : ℕ} (p : Fin d → ℂ) (u : Fin d → ℤ) (xi : ℝ) :
    (∑ mu, (-p mu) * ((xi : ℂ) * (u mu : ℂ))) =
      ∑ mu, p mu * ((xi : ℂ) * ((-u mu : ℤ) : ℂ)) := by
  apply Finset.sum_congr rfl
  intro mu _
  push_cast
  ring

example {d : ℕ} (u : Fin d → ℤ) :
    (fun mu => -(-u mu)) = u := by
  funext mu
  simp

example {d : ℕ} (p : Fin d → ℂ) :
    (fun mu => -p mu) = -p := by
  funext mu
  rfl

example {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℂ) :
    (∑ a, f (e a)) = ∑ b, f b := by
  exact Equiv.sum_comp e f
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "cmp99_cross_fibre_endpoint_phase_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "cmp99_cross_fibre_endpoint_phase_focal",
        [
            "lake",
            "build",
            "YangMills.RG."
            "BalabanCMP99SourceFlatQprimeCrossFibreEndpointPhase",
        ],
        None,
    ),
    (
        "cmp99_cross_fibre_endpoint_phase_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceFlatQprimeCrossFibreEndpointPhaseAudit.lean",
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
