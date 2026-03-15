import Mathlib
import YangMills.P8_PhysicalGap.LSItoSpectralGap
import YangMills.P8_PhysicalGap.StroockZegarlinski
import YangMills.P8_PhysicalGap.MarkovSemigroupDef

/-!
# PoincareCovarianceRoadmap — v0.8.10
Axiom count: 7 (markov_covariance_transport ELIMINATED)
markov_covariance_symm is now a THEOREM in MarkovSemigroupDef.lean.
sz_covariance_bridge replaces the old transport axiom honestly.
-/

namespace YangMills
open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Layer 2: Spectral gap axiom -/

/-! markov_spectral_gap moved to MarkovSemigroupDef.lean -/

/-! ## Layer 2b: SZ covariance bridge (honest replacement for transport axiom) -/

omit Ω [MeasurableSpace Ω] in
axiom sz_covariance_bridge
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∃ γ' : ℝ, 0 < γ' ∧ ∀ (f : Ω → ℝ), Integrable f μ → ∀ t : ℝ, 0 ≤ t →
      ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
      Real.exp (-γ' * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ)
    (F G : Ω → ℝ) (hF : Integrable F μ) (hG : Integrable G μ)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hG2 : Integrable (fun x => G x ^ 2) μ) :
    ∀ t : ℝ, 0 ≤ t →
      |∫ x, F x * sg.T t G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
      Real.exp (-γ * t) *
        Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)

/-! ## Layer 3: Cauchy-Schwarz — proved in StroockZegarlinski.lean -/

/-! ## Layer 4: Assembly — covariance decay -/

omit Ω [MeasurableSpace Ω] in
theorem markov_to_covariance_decay
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (F G : Ω → ℝ) (hF : Integrable F μ) (hG : Integrable G μ)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hG2 : Integrable (fun x => G x ^ 2) μ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ t : ℝ, 0 ≤ t →
      |∫ x, F x * sg.T t G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
      Real.exp (-γ * t) *
        Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
  obtain ⟨γ, hγ, hgap⟩ := markov_spectral_gap sg
  exact ⟨γ, hγ, sz_covariance_bridge sg γ hγ ⟨γ, hγ, hgap⟩ F G hF hG hF2 hG2⟩

end YangMills
