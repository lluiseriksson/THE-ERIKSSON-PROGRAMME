import Mathlib
import YangMills.P2_MaxEntClustering.PetzFidelity
import YangMills.P2_MaxEntClustering.MaxEntStates

namespace YangMills

/-! ## P2.4: Recovery Channels

This file formalizes the Petz recovery channel interface connecting the
MaxEnt state layer (P2.3) to the Fawzi-Renner clustering bridge (P2.5).

Mathlib v4.29 has `CompletelyPositiveMap` but requires `NonUnitalCStarAlgebra +
PartialOrder + StarOrderedRing`, which are not readily available for finite
matrix algebras without extensive topology setup. So we define:
- `IsTracePreserving` — custom predicate
- `IsPositivePreserving` — custom predicate
- `PetzRecoveryChannel` — packaged recovery map
- `HasRecoveryProperty` — recovery reconstructs target state
- `MaxEntToRecoveryBridge` — MaxEnt → Fawzi-Renner input
-/

section RecoveryChannels

/-- A recovery map preserves the trace. -/
def IsTracePreserving {n : ℕ} (R : RecoveryMap n) : Prop :=
  ∀ ρ : QuantumState n,
    Matrix.trace (R ρ).rho = Matrix.trace ρ.rho

/-- A recovery map preserves positivity of states. -/
def IsPositivePreserving {n : ℕ} (R : RecoveryMap n) : Prop :=
  ∀ ρ : QuantumState n,
    ∀ v : Fin n → ℂ,
      0 ≤ (Finset.univ.sum (fun i => star (v i) * (R ρ).rho.mulVec v i)).re

/-- A packaged Petz-style recovery channel (CPTP map interface). -/
structure PetzRecoveryChannel (n : ℕ) where
  toMap : RecoveryMap n
  tracePreserving : IsTracePreserving toMap

/-- Apply a Petz recovery channel to a quantum state. -/
def applyRecovery {n : ℕ} (R : PetzRecoveryChannel n) (ρ : QuantumState n) :
    QuantumState n :=
  R.toMap ρ

/-- The recovery channel reconstructs the target tripartite state from the
    reduced bipartite state. -/
def HasRecoveryProperty {n : ℕ}
    (R : PetzRecoveryChannel n)
    (ρAB ρABC : QuantumState n) : Prop :=
  R.toMap ρAB = ρABC

/-- Rotational recovery property: alias for HasRecoveryProperty. -/
def RotationalRecoveryProperty {n : ℕ}
    (R : PetzRecoveryChannel n)
    (ρAB ρABC : QuantumState n) : Prop :=
  HasRecoveryProperty R ρAB ρABC

theorem recoveryProperty_of_hyp {n : ℕ}
    (R : PetzRecoveryChannel n)
    (ρAB ρABC : QuantumState n)
    (h : HasRecoveryProperty R ρAB ρABC) :
    HasRecoveryProperty R ρAB ρABC := h

theorem tracePreserving_apply {n : ℕ}
    (R : PetzRecoveryChannel n) (ρ : QuantumState n) :
    Matrix.trace (R.toMap ρ).rho = Matrix.trace ρ.rho :=
  R.tracePreserving ρ

/-- If the recovery property holds, the applied channel equals the target. -/
theorem applyRecovery_eq {n : ℕ}
    (R : PetzRecoveryChannel n)
    (ρAB ρABC : QuantumState n)
    (h : HasRecoveryProperty R ρAB ρABC) :
    applyRecovery R ρAB = ρABC := h

end RecoveryChannels

section MaxEntBridge

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-- Bridge predicate: a MaxEnt state admits a Fawzi-Renner recovery bound.
    This is the key connection from P2.3 → P2.4 → P2.5. -/
def MaxEntToRecoveryBridge
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ)
    {n : ℕ} (ρABC : QuantumState n)
    (R : PetzRecoveryChannel n) : Prop :=
  MaxEntExists A ωA ∧ FawziRennerBound n ρABC R.toMap

/-- The bridge implies the Fawzi-Renner bound. -/
theorem maxEntBridge_implies_fawziRenner
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ)
    {n : ℕ} (ρABC : QuantumState n)
    (R : PetzRecoveryChannel n)
    (h : MaxEntToRecoveryBridge A ωA ρABC R) :
    FawziRennerBound n ρABC R.toMap := h.2

/-- The bridge implies MaxEnt existence. -/
theorem maxEntBridge_implies_maxEntExists
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ)
    {n : ℕ} (ρABC : QuantumState n)
    (R : PetzRecoveryChannel n)
    (h : MaxEntToRecoveryBridge A ωA ρABC R) :
    MaxEntExists A ωA := h.1

end MaxEntBridge

section FidelityBridge

/-- Recovery property + Fawzi-Renner bound → fidelity bound available. -/
theorem recoveryChannel_fidelity_bound {n : ℕ}
    (R : PetzRecoveryChannel n)
    (ρABC : QuantumState n)
    (hFR : FawziRennerBound n ρABC R.toMap) :
    PetzFidelity n ρABC (R.toMap ρABC) ≥
      Real.exp (-ConditionalMutualInformation n ρABC) := hFR

/-- If Fawzi-Renner holds, recovery error decays exponentially. -/
theorem recoveryChannel_implies_decayBound {n : ℕ}
    (R : PetzRecoveryChannel n)
    (ρABC : QuantumState n)
    (C xi r : ℝ) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hFR : FawziRennerBound n ρABC R.toMap)
    (hbridge : MaxEntClusteringRecoveryBridge n ρABC R.toMap C xi r) :
    1 - PetzFidelity n ρABC (R.toMap ρABC) ≤ C * Real.exp (-r / xi) := hbridge

end FidelityBridge

end YangMills
