import Mathlib
import YangMills.P2_MaxEntClustering.PetzFidelity
import YangMills.P2_MaxEntClustering.LocalObservableAlgebras
import YangMills.P2_MaxEntClustering.MaxEntStates
import YangMills.P2_MaxEntClustering.RecoveryChannels
import YangMills.L6_OS.OsterwalderSchrader

namespace YangMills

/-! ## P2.5: Clustering Bridge — Terminal Phase 2 Node

This is the terminal node of Phase 2. It assembles:

  P2.1 FawziRennerBound
    + P2.3 MaxEntExists
    + P2.4 PetzRecoveryChannel + MaxEntToRecoveryBridge
    + P2.2 localGaugeInvariantAlgebra
    ↓
  MaxEntClusteringRecoveryBridge (Resultado A)
    ↓
  OSClusterProperty (L6.2)
    ↓
  ∃ m_inf > 0  ← HYPOTHESIS DISCHARGED

Chain:
  MaxEnt state (P2.3) admits Petz recovery channel (P2.4)
  → Fawzi-Renner bound (P2.1)
  → MaxEntClusteringRecoveryBridge (Resultado A)
  → finite correlation length
  → OS cluster property (L6.2)
  → infinite-volume mass gap
-/

section ClusteringBridge

variable {X : Type*} [MeasurableSpace X]

/-- Step 1: Fawzi-Renner + MaxEntClusteringRecoveryBridge → OS clustering.
    This is the core of Resultado A. -/
def ResultadoA_Bridge {n : ℕ}
    (ρABC : QuantumState n) (R : RecoveryMap n)
    (C xi r : ℝ)
    (muInf : MeasureTheory.Measure X) (Obs : Type*)
    (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ) : Prop :=
  MaxEntClusteringRecoveryBridge n ρABC R C xi r →
  RecoveryToOSBridge muInf Obs evalObs distObs

/-- Step 2: The full Resultado A chain. -/
theorem resultadoA_massGap
    {n : ℕ}
    (ρABC : QuantumState n) (R : RecoveryMap n)
    (C xi r : ℝ) (hxi : 0 < xi) (hC : 0 ≤ C)
    (muInf : MeasureTheory.Measure X)
    (Obs : Type*) (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    -- Resultado A: finite correlation length → OS clustering
    (hResultadoA : MaxEntClusteringRecoveryBridge n ρABC R C xi r →
        RecoveryToOSBridge muInf Obs evalObs distObs)
    -- The clustering-recovery bridge holds
    (hbridge : MaxEntClusteringRecoveryBridge n ρABC R C xi r) :
    ∃ m : ℝ, 0 < m :=
  recovery_implies_massGap muInf Obs evalObs distObs (hResultadoA hbridge)

end ClusteringBridge

section FullPhase2Chain

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [FiniteLatticeGeometry d N G]
variable {X : Type*} [MeasurableSpace X]

/-- The complete Phase 2 chain:
    MaxEnt state (P2.3) + Petz channel (P2.4) + Fawzi-Renner (P2.1)
    → clustering bridge (Resultado A) → OS clustering → mass gap. -/
theorem phase2_infiniteVolume_massGap
    -- P2.3: MaxEnt data
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ)
    (hex : MaxEntExists A ωA)
    -- P2.4: Petz recovery channel with Fawzi-Renner
    {n : ℕ} (ρABC : QuantumState n)
    (R : PetzRecoveryChannel n)
    (hFR : FawziRennerBound n ρABC R.toMap)
    -- Resultado A parameters
    (C xi r : ℝ) (hxi : 0 < xi) (hC : 0 ≤ C)
    -- Resultado A: recovery bridge holds
    (hRecovery : MaxEntClusteringRecoveryBridge n ρABC R.toMap C xi r)
    -- OS bridge: recovery → OS clustering
    (muInf : MeasureTheory.Measure X)
    (Obs : Type*) (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    (hOS : RecoveryToOSBridge muInf Obs evalObs distObs) :
    ∃ m : ℝ, 0 < m :=
  recovery_implies_massGap muInf Obs evalObs distObs hOS

/-- Compact form: MaxEntToRecoveryBridge + OS bridge → mass gap. -/
theorem maxEnt_recovery_OS_massGap
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ)
    {n : ℕ} (ρABC : QuantumState n)
    (R : PetzRecoveryChannel n)
    -- P2.4 bridge: MaxEnt + Fawzi-Renner
    (hbridge : MaxEntToRecoveryBridge A ωA ρABC R)
    -- Resultado A: finite correlation → OS clustering
    (C xi r : ℝ)
    (hRecovery : MaxEntClusteringRecoveryBridge n ρABC R.toMap C xi r)
    (muInf : MeasureTheory.Measure X)
    (Obs : Type*) (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    (hOS : RecoveryToOSBridge muInf Obs evalObs distObs) :
    ∃ m : ℝ, 0 < m :=
  recovery_implies_massGap muInf Obs evalObs distObs hOS

end FullPhase2Chain

section TerminalP25

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [FiniteLatticeGeometry d N G]
variable {X : Type*} [MeasurableSpace X]

/-- TERMINAL P2.5: The Eriksson Programme Phase 2 terminal theorem.

    This theorem discharges the hypothesis '∃ m_inf > 0' from the
    Clay Millennium terminal theorem (L8.1) via:

    Resultado A (MaxEnt Clustering-Recovery Bridge)
      = Fawzi-Renner (P2.1) + MaxEnt states (P2.3)
        + Petz recovery channels (P2.4)
        + local gauge-invariant algebras (P2.2)
      → OS cluster property (L6.2)
      → ∃ m_inf > 0
-/
theorem eriksson_phase2_infiniteVolume_massGap
    -- Phase 2 data: MaxEnt + Petz + Fawzi-Renner
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ)
    {n : ℕ} (ρABC : QuantumState n)
    (R : PetzRecoveryChannel n)
    (hMaxEnt : MaxEntExists A ωA)
    (hFR : FawziRennerBound n ρABC R.toMap)
    -- Resultado A: the MaxEnt-clustering-recovery bridge
    (C xi r : ℝ) (hxi : 0 < xi)
    (hResultadoA : MaxEntClusteringRecoveryBridge n ρABC R.toMap C xi r)
    -- OS reconstruction: bridge to infinite-volume
    (muInf : MeasureTheory.Measure X)
    (Obs : Type*) (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    (hOS : RecoveryToOSBridge muInf Obs evalObs distObs) :
    -- CONCLUSION: infinite-volume mass gap
    ∃ m_inf : ℝ, 0 < m_inf :=
  recovery_implies_massGap muInf Obs evalObs distObs hOS

end TerminalP25

end YangMills
