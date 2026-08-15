#!/usr/bin/env python3
"""Colab diagnostic gate for the signed-alias endpoint phase bridge.

The immutable mathematical source is ``SOURCE_SHA``. This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol. A Mathlib-only repro
checks the period-pairing algebra before the expensive project focal.

Honest scope: this seals no row/column reflection, affine Fourier-negation
reindexing, finite synthesis, Brillouin periodization, regional ``B0``,
window-15 attainment or terminal field.
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
    "flat_qprime_endpoint_alias_phase_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-flat-qprime-endpoint-alias-phase-v2"
runner.SOURCE_SHA = "1fc19056f0a1fa0782924196687b84b074785679"
runner.ROOT = Path("/content/hrpoly-flat-qprime-endpoint-alias-phase")
runner.EVIDENCE = Path("/content/hrpoly-flat-qprime-endpoint-alias-phase-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-flat-qprime-endpoint-alias-phase-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-flat-qprime-endpoint-alias-phase-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimeEndpointAliasPhase.lean":
        "5da43c092180dbfa1e892e243b0384fff6fbcff517d03adc35cbef8ed964e9f4",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeEndpointAliasPhaseAudit.lean":
        "41adac323d2ea168de171c9d3d97594979e81f104e1ca0946ef7cb3376745ec3",
}

REPRO = HERE / "flat_qprime_endpoint_alias_phase_repro.lean"
REPRO.write_text(
    """import Mathlib

open scoped BigOperators

noncomputable def reproPhase {d : ℕ} (z : Fin d → ℂ) (u : Fin d → ℝ) : ℂ :=
  ∑ mu, z mu * (u mu : ℂ)

noncomputable def reproFineDisplacement {d : ℕ} (N : ℕ)
    (u : Fin d → ℤ) : Fin d → ℝ :=
  fun mu => (N : ℝ)⁻¹ * (u mu : ℝ)

def reproPairing {d : ℕ} (w u : Fin d → ℤ) : ℤ :=
  ∑ mu, w mu * u mu

example {d N : ℕ} [NeZero N] (z : Fin d → ℂ) (w u : Fin d → ℤ) :
    reproPhase
        (fun mu => z mu + (w mu : ℂ) *
          (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ)))
        (reproFineDisplacement N u) =
      reproPhase z (reproFineDisplacement N u) +
        (((2 * Real.pi : ℝ) : ℂ) * (reproPairing w u : ℂ)) := by
  unfold reproPhase reproFineDisplacement reproPairing
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  have hN : (N : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  field_simp [hN]

example {d N : ℕ} [NeZero N] (z : Fin d → ℂ) (w u : Fin d → ℤ) :
    Complex.exp (Complex.I * reproPhase
        (fun mu => z mu + (w mu : ℂ) *
          (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ)))
        (reproFineDisplacement N u)) =
      Complex.exp (Complex.I * reproPhase z (reproFineDisplacement N u)) := by
  rw [show reproPhase
      (fun mu => z mu + (w mu : ℂ) *
        (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ)))
      (reproFineDisplacement N u) =
        reproPhase z (reproFineDisplacement N u) +
          (((2 * Real.pi : ℝ) : ℂ) * (reproPairing w u : ℂ)) by
    unfold reproPhase reproFineDisplacement reproPairing
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mu _
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    field_simp [hN],
    mul_add, Complex.exp_add]
  rw [show
    Complex.exp (Complex.I * (((2 * Real.pi : ℝ) : ℂ) *
        (reproPairing w u : ℂ))) = 1 by
    rw [show
      Complex.I * (((2 * Real.pi : ℝ) : ℂ) * (reproPairing w u : ℂ)) =
        ((reproPairing w u : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I (reproPairing w u),
    mul_one]
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "flat_qprime_endpoint_alias_phase_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "flat_qprime_endpoint_alias_phase_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointAliasPhase",
        ],
        None,
    ),
    (
        "flat_qprime_endpoint_alias_phase_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceFlatQprimeEndpointAliasPhaseAudit.lean",
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
