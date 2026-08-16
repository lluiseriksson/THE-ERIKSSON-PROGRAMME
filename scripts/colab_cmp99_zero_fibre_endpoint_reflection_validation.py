#!/usr/bin/env python3
"""Colab diagnostic gate for the zero-fibre endpoint reflection.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only reproduction checks the signed
endpoint phase and whole-carrier equivalence reindexing before the expensive
project focal.

Honest scope: this validates only the zero-coarse-fibre reflection and its
complete finite alias sum.  It does not combine the zero/nonzero branches,
identify a Brillouin integral, build regional ``B0``, attain window 15,
discharge a terminal field or inhabit ``TermSource``.
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
    "cmp99_zero_fibre_endpoint_reflection_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-zero-fibre-endpoint-reflection-v1"
runner.SOURCE_SHA = "34f75aa60e39301a7fd281054513bfce5fe99cc2"
runner.ROOT = Path("/content/hrpoly-cmp99-zero-fibre-endpoint-reflection")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-zero-fibre-endpoint-reflection-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-zero-fibre-endpoint-reflection-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-zero-fibre-endpoint-reflection-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimeZeroFibreEndpointReflection.lean":
        "2f70d3506436590e77654c9e08670f32d66965d0bc413033bc2c9223e0138329",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeZeroFibreEndpointReflectionAudit.lean":
        "74f5dc0d70bc3fac6f0297aaf032b32310809b87641f5bfa055d355c4212de2b",
}

REPRO = HERE / "cmp99_zero_fibre_endpoint_reflection_repro.lean"
REPRO.write_text(
    """import Mathlib

example {d : ℕ} (p : Fin d → ℂ) (u : Fin d → ℤ) (xi : ℝ) :
    (∑ mu, (-p mu) * ((xi : ℂ) * (u mu : ℂ))) =
      ∑ mu, p mu * ((xi : ℂ) * ((-u mu : ℤ) : ℂ)) := by
  apply Finset.sum_congr rfl
  intro mu _
  push_cast
  ring

example {A : Type*} [Fintype A] (e : A ≃ A) (f : A → ℂ) :
    (∑ a, f (e a)) = ∑ a, f a := by
  exact Equiv.sum_comp e f

example {d : ℕ} (u : Fin d → ℤ) :
    (fun mu => -(-u mu)) = u := by
  funext mu
  simp
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "cmp99_zero_fibre_endpoint_reflection_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "cmp99_zero_fibre_endpoint_reflection_focal",
        [
            "lake",
            "build",
            "YangMills.RG."
            "BalabanCMP99SourceFlatQprimeZeroFibreEndpointReflection",
        ],
        None,
    ),
    (
        "cmp99_zero_fibre_endpoint_reflection_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceFlatQprimeZeroFibreEndpointReflectionAudit.lean",
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
