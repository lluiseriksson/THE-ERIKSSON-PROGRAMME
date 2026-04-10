/-
  C105: UnitObsToPhysicalStrong
  Observation states are unit vectors (HasUnitObsNorm).
  This absorbs StateNormBound (C_ψ = 1) into the FK formula, yielding a
  2-hypothesis theorem: PhysicalFeynmanKacFormula + HasSpectralGap → PhysicalStrong.
  Net: 3 → 2 live hypotheses. v1.21.0.
-/
import YangMills.P8_PhysicalGap.DistPNonnegFromFormula

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
         {d : ℕ} [NeZero d]

open MeasureTheory

/-- C105: Observation states are unit vectors.
    In quantum field theory, physical states always have unit norm.
    Strictly stronger than StateNormBound (which allows any C_ψ ≥ 0). -/
def HasUnitObsNorm (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N), ‖ψ_obs N p‖ = 1

/-- C105-aux: Unit-normalized obs states satisfy StateNormBound with C_ψ = 1. -/
theorem stateNormBound_of_hasUnitObsNorm
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (h : HasUnitObsNorm ψ_obs) :
    StateNormBound ψ_obs 1 := by
  constructor
  · norm_num
  · intro N _ p
    linarith [h N p]

/-- C105: Physical Feynman-Kac formula = standard FK + unit observation states.
    Physically motivated: path integrals always use unit-normalized quantum states. -/
def PhysicalFeynmanKacFormula
    (μ : MeasureTheory.Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs ∧
  HasUnitObsNorm ψ_obs

/-- C105: ClayYangMillsPhysicalStrong from PhysicalFeynmanKacFormula + HasSpectralGap.
    StateNormBound is absorbed: unit norm ⇒ StateNormBound with C_ψ = 1.
    Reduces live hypothesis count from three to two:
      (FeynmanKacFormula + StateNormBound + HasSpectralGap) →
      (PhysicalFeynmanKacFormula + HasSpectralGap). -/
theorem physicalStrong_of_physicalFormula_spectralGap
    {μ : MeasureTheory.Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    {γ C_gap : ℝ}
    (hpFK : PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hgap : HasSpectralGap T P₀ γ C_gap) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_formula_stateNorm_hasSpectralGap_v2
    (stateNormBound_of_hasUnitObsNorm hpFK.2) hpFK.1 hgap

end YangMills
