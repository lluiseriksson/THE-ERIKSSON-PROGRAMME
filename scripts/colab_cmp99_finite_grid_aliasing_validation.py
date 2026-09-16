#!/usr/bin/env python3
"""Colab diagnostic gate for exact finite-grid Fourier aliasing.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only reproduction checks the finite
sum / infinite sum interchange before the expensive project focal.

Honest scope: this validates only the generic algebraic aliasing substrate.
It does not assert the physical Fourier-series expansion of the CMP89
integrand, construct regional ``B0``, attain window 15, discharge a terminal
field or inhabit ``TermSource``.
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
    "cmp99_finite_grid_aliasing_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-finite-grid-aliasing-v2"
runner.SOURCE_SHA = "534493728038813f3772f8b3b073237f4da1884e"
runner.ROOT = Path("/content/hrpoly-cmp99-finite-grid-aliasing")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-finite-grid-aliasing-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-finite-grid-aliasing-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-finite-grid-aliasing-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99FlatFiniteGridAliasing.lean":
        "de04ca53ce8b753e80514e607f0b47ae6c6cf41811b353e60030b21f4a5a2a52",
    "YangMills/RG/BalabanCMP99FlatFiniteGridAliasingAudit.lean":
        "1207c5881c98379753407f426392100b08e44c503d64ce03cc2c3daba7b5290b",
}

REPRO = HERE / "cmp99_finite_grid_aliasing_repro.lean"
REPRO.write_text(
    """import Mathlib

open scoped BigOperators

noncomputable section

example {ι κ : Type*} [Fintype κ]
    (f : κ → ι → ℂ) (hf : ∀ k, Summable (f k)) :
    (∑' i, ∑ k, f k i) = ∑ k, ∑' i, f k i := by
  simpa using Summable.tsum_finsetSum
    (s := (Finset.univ : Finset κ))
    (f := fun k i => f k i)
    (fun k _ => hf k)

example {ι : Type*} (s : Set ι) (f : ι → ℂ) :
    (∑' i, s.indicator f i) = ∑' i : s, f i := by
  exact (tsum_subtype s f).symm
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "cmp99_finite_grid_aliasing_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "cmp99_finite_grid_aliasing_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99FlatFiniteGridAliasing",
        ],
        None,
    ),
    (
        "cmp99_finite_grid_aliasing_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99FlatFiniteGridAliasingAudit.lean",
        ],
        7,
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
