import Mathlib
import YangMills.P8_PhysicalGap.MarkovSemigroupDef
import YangMills.P8_PhysicalGap.PoincareCovarianceRoadmap

namespace YangMills
open MeasureTheory Real Filter Set

section
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Step 1: Mean preservation -/

theorem markov_preserves_integral
    (sg : MarkovSemigroup μ) (f : Ω → ℝ)
    (hf : Integrable f μ) (t : ℝ) :
    ∫ x, sg.T t f x ∂μ = ∫ x, f x ∂μ :=
  sg.T_stat t f hf

/-! ## Auxiliary: T commutes with centering -/

lemma T_sub_const
    (sg : MarkovSemigroup μ) (t : ℝ) (f : Ω → ℝ) (m : ℝ) :
    sg.T t (fun x => f x - m) = fun x => sg.T t f x - m := by
  calc sg.T t (fun x => f x - m)
      = sg.T t (fun x => 1 * f x + (-1) * (fun _ => m) x) := by
          congr 1; ext x; ring
    _ = fun x => 1 * sg.T t f x + (-1) * sg.T t (fun _ => m) x :=
          sg.T_linear t f (fun _ => m) 1 (-1)
    _ = fun x => 1 * sg.T t f x + (-1) * m := by
          rw [sg.T_const t m]
    _ = fun x => sg.T t f x - m := by
          ext x; ring

/-! ## Step 2: Variance = ‖f - mean‖₂² -/

theorem variance_eq_l2_sq_centered
    (f : Ω → ℝ)
    (hf  : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ =
    ∫ x, f x ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2 := by
  set m : ℝ := ∫ y, f y ∂μ
  have hcross : Integrable (fun x => (2 * m) * f x) μ := hf.const_mul (2 * m)
  have hconst : Integrable (fun _ : Ω => m ^ 2) μ := integrable_const _
  have h_expand : (fun x => (f x - m) ^ 2) =ᵐ[μ]
      (fun x => (f x ^ 2 - (2 * m) * f x) + m ^ 2) :=
    ae_of_all _ fun x => by ring
  have hm_const : ∫ x, m ^ 2 ∂μ = m ^ 2 := by
    rw [integral_const, smul_eq_mul]
    change (μ Set.univ).toReal * m ^ 2 = m ^ 2
    rw [measure_univ, ENNReal.toReal_one, one_mul]
  have hm_mul : ∫ x, (2 * m) * f x ∂μ = (2 * m) * m := by
    rw [integral_const_mul]
  calc ∫ x, (f x - m) ^ 2 ∂μ
      = ∫ x, ((f x ^ 2 - (2 * m) * f x) + m ^ 2) ∂μ :=
          integral_congr_ae h_expand
    _ = ∫ x, (f x ^ 2 - (2 * m) * f x) ∂μ + ∫ x, m ^ 2 ∂μ :=
          integral_add (hf2.sub hcross) hconst
    _ = (∫ x, f x ^ 2 ∂μ - ∫ x, (2 * m) * f x ∂μ) + ∫ x, m ^ 2 ∂μ := by
          rw [integral_sub hf2 hcross]
    _ = (∫ x, f x ^ 2 ∂μ - (2 * m) * m) + m ^ 2 := by
          rw [hm_mul, hm_const]
    _ = ∫ x, f x ^ 2 ∂μ - m ^ 2 := by ring

/-! ## Step 3: Poincaré bound -/

theorem varT_poincare_bound
    (sg : MarkovSemigroup μ)
    (γ : ℝ) (hγ : 0 < γ)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (t : ℝ) (ht : 0 ≤ t)
    (hgap : ∀ g : Ω → ℝ,
        ∫ x, g x ∂μ = 0 →
        Integrable g μ →
        Integrable (fun x => g x ^ 2) μ →
        ∫ x, (sg.T t g x) ^ 2 ∂μ ≤
        Real.exp (-2 * γ * t) * ∫ x, g x ^ 2 ∂μ) :
    ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
    Real.exp (-2 * γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
  set m := ∫ x, f x ∂μ
  -- g = f - m is centered
  have hg_center : ∫ x, (f x - m) ∂μ = 0 := by
    rw [integral_sub hf (integrable_const m), integral_const, smul_eq_mul]
    change ∫ x, f x ∂μ - (μ Set.univ).toReal * m = 0
    rw [measure_univ, ENNReal.toReal_one, one_mul]
    exact sub_self m
  have hg_int : Integrable (fun x => f x - m) μ := hf.sub (integrable_const m)
  -- g² integrable via algebraic expansion
  have hg2_int : Integrable (fun x => (f x - m) ^ 2) μ := by
    have h_eq : (fun x => (f x - m) ^ 2) =ᵐ[μ]
        (fun x => (f x ^ 2 - (2 * m) * f x) + m ^ 2) :=
      ae_of_all _ fun x => by ring
    exact (hf2.sub (hf.const_mul (2 * m))).add (integrable_const _) |>.congr h_eq.symm
  -- T_t(f - m) = T_t f - m
  have hTsub : sg.T t (fun x => f x - m) = fun x => sg.T t f x - m :=
    T_sub_const sg t f m
  -- LHS: ∫(T_t f - m)² = ∫(T_t(f-m))²
  have hlhs : ∫ x, (sg.T t f x - m) ^ 2 ∂μ =
              ∫ x, (sg.T t (fun y => f y - m) x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    have hx := congr_fun hTsub x
    rw [hx]
  rw [hlhs]
  exact hgap (fun x => f x - m) hg_center hg_int hg2_int

end

/-! ## Variance decay — proved from markov_spectral_gap -/

/-- Variance decay: derived from markov_spectral_gap via γ₀/2 witness.
    Replaces the former axiom markov_variance_decay. -/
theorem markov_variance_decay
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) :
    ∃ γ : ℝ, 0 < γ ∧
    ∀ f : Ω → ℝ, Integrable f μ →
    Integrable (fun x => f x ^ 2) μ →
    ∀ t : ℝ, 0 ≤ t →
      ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
      Real.exp (-2 * γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
  obtain ⟨γ₀, hγ₀, hgap₀⟩ := markov_spectral_gap sg
  refine ⟨γ₀ / 2, half_pos hγ₀, fun f hf _hf2 t ht => ?_⟩
  have key := hgap₀ f hf t ht
  calc ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ
      ≤ Real.exp (-γ₀ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := key
    _ = Real.exp (-2 * (γ₀ / 2) * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
        congr 1; congr 1; ring

end YangMills
