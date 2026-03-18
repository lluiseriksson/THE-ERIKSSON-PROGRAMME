import Mathlib
import YangMills.P8_PhysicalGap.MarkovSemigroupDef
import YangMills.P8_PhysicalGap.MarkovVarianceDecay
import YangMills.P8_PhysicalGap.CovarianceLemmas

/-!
# PoincareCovarianceRoadmap — v0.8.40
sz_covariance_bridge: proved from markov_variance_decay + Cauchy-Schwarz.
-/

namespace YangMills
open MeasureTheory Real Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

omit Ω [MeasurableSpace Ω] in
theorem sz_covariance_bridge
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (F G : Ω → ℝ) (hF : Integrable F μ) (hG : Integrable G μ)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hG2 : Integrable (fun x => G x ^ 2) μ) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ t : ℝ, 0 ≤ t →
        |∫ x, F x * sg.T t G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
        Real.exp (-γ * t) *
          Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
  obtain ⟨γ, hγ, hdecay⟩ := markov_variance_decay sg
  refine ⟨γ, hγ, fun t ht => ?_⟩
  have hTG  : Integrable (sg.T t G) μ := sg.T_integrable t G hG
  have hTG2 : Integrable (fun x => sg.T t G x ^ 2) μ := sg.T_sq_integrable t G hG2
  have hstat : ∫ x, sg.T t G x ∂μ = ∫ x, G x ∂μ := sg.T_stat t G hG
  have hFv : Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ := by
    have h_eq : (fun x => (F x - ∫ y, F y ∂μ) ^ 2) =ᵐ[μ]
        (fun x => F x ^ 2 - (2 * ∫ y, F y ∂μ) * F x + (∫ y, F y ∂μ) ^ 2) :=
      ae_of_all _ fun x => by ring
    exact (hF2.sub (hF.const_mul _)).add (integrable_const _) |>.congr h_eq.symm
  have hTGv : Integrable (fun x => (sg.T t G x - ∫ y, sg.T t G y ∂μ) ^ 2) μ := by
    have h_eq : (fun x => (sg.T t G x - ∫ y, sg.T t G y ∂μ) ^ 2) =ᵐ[μ]
        (fun x => sg.T t G x ^ 2 - (2 * ∫ y, sg.T t G y ∂μ) * sg.T t G x
          + (∫ y, sg.T t G y ∂μ) ^ 2) :=
      ae_of_all _ fun x => by ring
    exact (hTG2.sub (hTG.const_mul _)).add (integrable_const _) |>.congr h_eq.symm
  have hFGT : Integrable (fun x => F x * sg.T t G x) μ := by
    apply (hF2.add hTG2).mono' (hF.aestronglyMeasurable.mul hTG.aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      simp only [Real.norm_eq_abs, abs_mul]
      have h2ab : 2 * (|F x| * |sg.T t G x|) ≤ |F x| ^ 2 + |sg.T t G x| ^ 2 := by
        nlinarith [sq_nonneg (|F x| - |sg.T t G x|)]
      have habs : |F x| * |sg.T t G x| ≤ |F x| ^ 2 + |sg.T t G x| ^ 2 := by
        nlinarith [h2ab, mul_nonneg (abs_nonneg (F x)) (abs_nonneg (sg.T t G x))]
      simpa [sq_abs] using habs
  -- Cauchy-Schwarz then rewrite ∫ T_t G → ∫ G
  have hCS_raw := covariance_le_sqrt_var F (sg.T t G) hF hTG hFv hTGv hFGT
  have hCS : |∫ x, F x * sg.T t G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (sg.T t G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
    rwa [hstat] at hCS_raw
  -- Variance decay
  have hdec := hdecay G hG hG2 t ht
  -- √(exp(-2γt)) = exp(-γt)
  have hsqrt_exp : Real.sqrt (Real.exp (-2 * γ * t)) = Real.exp (-γ * t) := by
    rw [show Real.exp (-2 * γ * t) = Real.exp (-γ * t) ^ 2 from by
          rw [sq, ← Real.exp_add]; congr 1; ring,
        Real.sqrt_sq (Real.exp_nonneg _)]
  -- √(Var(T_t G, mean=∫G)) ≤ exp(-γt) · √(Var(G))
  have hsqrt_decay :
      Real.sqrt (∫ x, (sg.T t G x - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
      Real.exp (-γ * t) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
    calc Real.sqrt (∫ x, (sg.T t G x - ∫ y, G y ∂μ) ^ 2 ∂μ)
        ≤ Real.sqrt (Real.exp (-2 * γ * t) * ∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
            apply Real.sqrt_le_sqrt
            simpa [hstat] using hdec
      _ = Real.sqrt (Real.exp (-2 * γ * t)) *
            Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) :=
            Real.sqrt_mul (Real.exp_nonneg _) _
      _ = Real.exp (-γ * t) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
            rw [hsqrt_exp]
  -- Assembly
  calc |∫ x, F x * sg.T t G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)|
      ≤ Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (sg.T t G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := hCS
    _ ≤ Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          (Real.exp (-γ * t) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)) :=
          mul_le_mul_of_nonneg_left hsqrt_decay (Real.sqrt_nonneg _)
    _ = Real.exp (-γ * t) *
          Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by ring

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
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) :=
  sz_covariance_bridge sg F G hF hG hF2 hG2

end YangMills
