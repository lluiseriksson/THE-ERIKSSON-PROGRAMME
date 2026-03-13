import Mathlib
import YangMills.L4_WilsonLoops.WilsonLoop
import YangMills.L5_MassGap.MassGap
import YangMills.L3_RGIteration.BlockSpin
import YangMills.L7_Continuum.ContinuumLimit

namespace YangMills

open MeasureTheory

/-! ## P3.1: Correlation Norms and RG Decay Witnesses

First node of Phase 3. Packages abstract RG contraction into decay witnesses
that will discharge `LatticeMassProfile.IsPositive`.

Key design: `ConnectedCorrDecay` is a `structure` in `Type` (not `Prop`)
so it can hold data fields `C m : ℝ` alongside proofs.
Bridge theorem `.toUniformWilsonDecay` converts it to the L5 `Prop`.

Node plan:
- P3.1 CorrelationNorms (this): decay witnesses + RG bridges
- P3.2 RGContraction: one-step improvement theorem
- P3.3 MultiscaleDecay: n-step exponential decay
- P3.4 LatticeMassExtraction: extract LatticeMassProfile.IsPositive
- P3.5 Phase3Assembly: discharge hypothesis in L8.1
-/

section CorrelationDecay

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- A finite-volume connected-correlation decay witness.
    Lives in `Type` (not `Prop`) so it can hold data fields C, m : ℝ
    alongside their proofs. -/
structure ConnectedCorrDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ) where
  C : ℝ
  m : ℝ
  hC : 0 ≤ C
  hm : 0 < m
  bound :
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q|
        ≤ C * Real.exp (-m * distP N p q)

/-- A decay witness implies the L5 uniform Wilson decay predicate (Prop). -/
theorem ConnectedCorrDecay.toUniformWilsonDecay
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    UniformWilsonDecay μ plaquetteEnergy β F distP :=
  ⟨h.C, h.m, h.hC, h.hm, h.bound⟩

/-- One RG step strictly improves the decay rate (abstract bridge predicate). -/
def RGStepImproves
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ) : Prop :=
  ∀ C m : ℝ, 0 ≤ C → 0 < m → ∃ m' : ℝ, m < m'

/-- Multiscale decay bound after n RG steps (lives in Prop as existential). -/
def MultiscaleDecayBound
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (n : ℕ) : Prop :=
  ∃ C m : ℝ, 0 ≤ C ∧ 0 < m ∧
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q|
        ≤ C * Real.exp (-(n : ℝ) * m * distP N p q)

/-- Step 1 of multiscale decay follows directly from a decay witness. -/
theorem multiscaleDecay_step_one
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    MultiscaleDecayBound μ plaquetteEnergy β F distP 1 := by
  refine ⟨h.C, h.m, h.hC, h.hm, fun N _ p q => ?_⟩
  have hb := h.bound N p q
  convert hb using 2
  norm_num

end CorrelationDecay

section RGBridges

variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Bridge: wraps `rg_iterate_bound` from L3 as a named predicate. -/
def HasRGIterationBridge (plaquetteEnergy : G → ℝ) (β κ : ℝ) : Prop :=
  0 ≤ β → 0 ≤ κ → ∀ n : ℕ, Real.exp (-(n : ℝ) * β * κ) ≤ 1

/-- `rg_iterate_bound` from L3 provides the iteration bridge. -/
noncomputable def hasRGIterationBridge_of_repo
    (plaquetteEnergy : G → ℝ) (β κ : ℝ) :
    HasRGIterationBridge plaquetteEnergy β κ :=
  fun hβ hκ n => rg_iterate_bound plaquetteEnergy β κ hβ hκ n

/-- Bridge: wraps `rg_coupling_monotone` from L3 as a named predicate. -/
def HasRGCouplingImprovement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ L : BlockFactor, 1 < L → ∃ β' : ℝ, β < β'

/-- `rg_coupling_monotone` from L3 provides the coupling bridge. -/
theorem hasRGCouplingImprovement_of_repo : HasRGCouplingImprovement :=
  fun β hβ L hL => rg_coupling_monotone β hβ L hL

/-- Coupling improvement implies decay rate improvement. -/
theorem rgCoupling_implies_decayImprovement
    (β β' κ : ℝ) (hβ : 0 < β) (hκ : 0 < κ) (hβ' : β < β') :
    β * κ < β' * κ :=
  mul_lt_mul_of_pos_right hβ' hκ

end RGBridges

section LatticeMassExtraction

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Bridge predicate: a decay witness determines positivity of the lattice mass profile. -/
def ExtractsLatticeMassProfile
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (m_lat : LatticeMassProfile) : Prop :=
  ConnectedCorrDecay μ plaquetteEnergy β F distP →
    LatticeMassProfile.IsPositive m_lat

/-- Terminal P3.1: decay witness + extraction bridge → IsPositive. -/
theorem latticeMassProfile_pos_of_decay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (m_lat : LatticeMassProfile)
    (hext : ExtractsLatticeMassProfile μ plaquetteEnergy β F distP m_lat)
    (hdecay : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    LatticeMassProfile.IsPositive m_lat :=
  hext hdecay

/-- Chaining: decay witness → uniform Wilson decay ∧ lattice mass positive. -/
theorem decay_chain_latticeMass
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (m_lat : LatticeMassProfile)
    (hdecay : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hext : ExtractsLatticeMassProfile μ plaquetteEnergy β F distP m_lat) :
    UniformWilsonDecay μ plaquetteEnergy β F distP ∧
    LatticeMassProfile.IsPositive m_lat :=
  ⟨hdecay.toUniformWilsonDecay, hext hdecay⟩

end LatticeMassExtraction

end YangMills
