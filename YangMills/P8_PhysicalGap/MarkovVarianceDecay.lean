import Mathlib
import YangMills.P8_PhysicalGap.MarkovSemigroupDef

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

/-! ## Step 2: Variance = ‖f - mean‖₂² -/

theorem variance_eq_l2_sq_centered
    (f : Ω → ℝ)
    (hf  : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ =
    ∫ x, f x ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2 := by
  set m := ∫ x, f x ∂μ
  have hm : Integrable (fun _ : Ω => m) μ := integrable_const m
  have hfm : Integrable (fun x => f x - m) μ := hf.sub hm
  have hfm2 : Integrable (fun x => (f x - m) ^ 2) μ := by
    apply Integrable.mono (hf2.add (integrable_const (m ^ 2)))
    · exact hfm.aestronglyMeasurable.pow_const 2
    · exact ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, abs_pow]
        nlinarith [abs_nonneg (f x - m), sq_abs (f x - m)]
  calc ∫ x, (f x - m) ^ 2 ∂μ
      = ∫ x, (f x ^ 2 - 2 * m * f x + m ^ 2) ∂μ := by
        congr 1; ext x; ring
    _ = ∫ x, f x ^ 2 ∂μ - 2 * m * ∫ x, f x ∂μ + m ^ 2 := by
        rw [integral_add (hf2.sub (hf.const_mul (2 * m))) (integrable_const _),
            integral_sub hf2 (hf.const_mul (2 * m))]
        simp [integral_const, integral_const_mul, measure_univ]
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
  set g := fun x => f x - m
  have hg_center : ∫ x, g x ∂μ = 0 := by
    simp [g, integral_sub hf (integrable_const m)]
  have hg_int : Integrable g μ := hf.sub (integrable_const m)
  have hg2_int : Integrable (fun x => g x ^ 2) μ := by
    apply Integrable.mono (hf2.add (integrable_const (m ^ 2)))
    · exact hg_int.aestronglyMeasurable.pow_const 2
    · exact ae_of_all _ fun x => by
        simp only [g, Real.norm_eq_abs, abs_pow]
        nlinarith [abs_nonneg (f x - m), sq_abs (f x - m)]
  have hTg_eq : ∀ x, sg.T t g x = sg.T t f x - m := by
    intro x
    have hlin := congr_fun (sg.T_linear t f (fun _ => m) 1 (-1)) x
    have hc   := congr_fun (sg.T_const t m) x
    simp only [one_mul, neg_mul, one_mul, g] at *
    linarith
  have hlhs : ∫ x, (sg.T t f x - m) ^ 2 ∂μ =
              ∫ x, (sg.T t g x) ^ 2 ∂μ :=
    integral_congr_ae (ae_of_all _ fun x => by rw [hTg_eq])
  rw [hlhs]
  exact hgap g hg_center hg_int hg2_int

end

/-! ## Variance decay axiom (Gronwall target) -/

axiom markov_variance_decay
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ f : Ω → ℝ, Integrable f μ →
    Integrable (fun x => f x ^ 2) μ →
    ∀ t : ℝ, 0 ≤ t →
      ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
      Real.exp (-2 * γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

end YangMills
