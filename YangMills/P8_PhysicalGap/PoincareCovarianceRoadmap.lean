import Mathlib
import YangMills.P8_PhysicalGap.LSItoSpectralGap
import YangMills.P8_PhysicalGap.MarkovSemigroupDef
import YangMills.P8_PhysicalGap.CovarianceLemmas

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
/-- SZ covariance bridge: proved from markov_variance_decay + Cauchy-Schwarz.
    Replaces the former axiom sz_covariance_bridge. -/
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
  -- Semigroup integrability
  have hTG  : Integrable (sg.T t G) μ := sg.T_integrable t G hG
  have hTG2 : Integrable (fun x => sg.T t G x ^ 2) μ := sg.T_sq_integrable t G hG2
  -- Variance integrabilities via algebraic expansion
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
  -- F * T_t G integrability via |ab| ≤ a² + b²
  have hFGT : Integrable (fun x => F x * sg.T t G x) μ := by
    apply (hF2.add hTG2).mono' (hF.aestronglyMeasurable.mul hTG.aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      simp only [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_abs (F x), sq_abs (sg.T t G x), sq_nonneg (|F x| - |sg.T t G x|)]
  -- Cauchy-Schwarz for covariance
  have hstat : ∫ x, sg.T t G x ∂μ = ∫ x, G x ∂μ := sg.T_stat t G hG
  have hCS := covariance_le_sqrt_var F (sg.T t G) hFv hTGv hFGT
  rw [hstat] at hCS
  -- Variance decay: Var(T_t G) ≤ exp(-2γt) · Var(G)
  have hdec := hdecay G hG hG2 t ht
  -- √(exp(-2γt) · VarG) = exp(-γt) · √VarG
  have hsqrt_exp : Real.sqrt (Real.exp (-2 * γ * t)) = Real.exp (-γ * t) := by
    have hmul : Real.exp (-2 * γ * t) = Real.exp (-γ * t) * Real.exp (-γ * t) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hmul, Real.sqrt_mul (Real.exp_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _)]
  have hsqrt_decay :
      Real.sqrt (∫ x, (sg.T t G x - ∫ y, sg.T t G y ∂μ) ^ 2 ∂μ) ≤
      Real.exp (-γ * t) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
    have hTGv_mean : ∫ y, sg.T t G y ∂μ = ∫ y, G y ∂μ := hstat
    rw [hTGv_mean]
    calc Real.sqrt (∫ x, (sg.T t G x - ∫ y, G y ∂μ) ^ 2 ∂μ)
        ≤ Real.sqrt (Real.exp (-2 * γ * t) * ∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) :=
            Real.sqrt_le_sqrt hdec
      _ = Real.sqrt (Real.exp (-2 * γ * t)) *
            Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) :=
            Real.sqrt_mul (Real.exp_nonneg _) _
      _ = Real.exp (-γ * t) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
            rw [hsqrt_exp]
  -- Assemble
  calc |∫ x, F x * sg.T t G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)|
      ≤ Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (sg.T t G x - ∫ y, sg.T t G y ∂μ) ^ 2 ∂μ) := hCS
    _ ≤ Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          (Real.exp (-γ * t) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)) :=
          mul_le_mul_of_nonneg_left hsqrt_decay (Real.sqrt_nonneg _)
    _ = Real.exp (-γ * t) *
          Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by ring

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
  exact sz_covariance_bridge sg F G hF hG hF2 hG2

end YangMills
